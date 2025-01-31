

using Catlab
import Catlab: neighbors


concatMap(f, xs) = vcat(map(f, xs)...)

function neighbors(g::SymmetricReflexiveGraph, v::Int)
    # This is because Catlab doesn't define neighbors for SRGs for some reason?
    F = FinFunctor(Dict(:V => :V, :E => :E), Dict(:src => :src, :tgt => :tgt, :inv => :inv), SchSymmetricGraph, SchSymmetricReflexiveGraph)
    ΔF = DeltaMigration(F)
    gm = migrate(SymmetricGraph, g, ΔF)

    return neighbors(gm, v)
end

function closed_neighborhood(g, vs_in)
    #list of neighbors of each v ∈ vs
    nvs = map(v -> collect(neighbors(g, v)), vs_in)
    # {v ∈ vs_in } ⋃ ⋃ᵥ N(v)
    vs = union(vs_in, foldl(union, nvs))
    #give me all the edges :) 
    q = (v, ns) -> foldl((acc, x) -> vcat(acc, collect(edges(g, v, x))), ns; init=Int64[])

    out_edges = concatMap(t -> q(t, union(nvs...)), vs_in)
    #out_edges = concatMap(t -> q(t...), zip(vs_in, nvs))
    #   {v->y | v ∈ vs_in}    ∪    {z -> v | v ∈ vs_in}      ∪   {v->v | v ∈ vs_in}
    es = union(out_edges, map(x -> inv(g, x), out_edges), map(x -> g[:refl][x], vs))

    return Subobject(g, V=vs, E=es)
end


function contract_vertices(g, v1, v2)
    F = FinFunctor(Dict(:V => :V, :E => :E), Dict(:src => :src, :tgt => :tgt, :inv => :inv), SchSymmetricGraph, SchSymmetricReflexiveGraph)
    ΔF = DeltaMigration(F)
    gm = migrate(SymmetricGraph, g, ΔF)


    nv1 = collect(neighbors(gm, v1))
    nv2 = collect(neighbors(gm, v2))

    #println(nv1)
    #println(nv2)

    common_neighbors = filter(x -> x in nv2, nv1)

    #println(common_neighbors)

    es1 = foldl((acc, x) -> vcat(acc, collect(edges(g, v1, x))), common_neighbors; init=Int64[])
    es2 = foldl((acc, x) -> vcat(acc, collect(edges(g, v2, x))), common_neighbors; init=Int64[])


    es1 = vcat(es1, map(x -> inv(g, x), es1), [g[:refl][v1]])
    es2 = vcat(es2, map(x -> inv(g, x), es2), [g[:refl][v2]])

    #println(es1)
    #rintln(es2)

    f1 = hom(Subobject(g, V=vcat([v1], common_neighbors), E=es1))
    f2 = hom(Subobject(g, V=vcat([v2], common_neighbors), E=es2))

    codom(f1) == codom(f2) || error("Failure!")

    res = coequalizer(f1, f2)

    return apex(res), legs(res)[1]
end

function boxtimes(g_in::SymmetricReflexiveGraph)
    pr_gr = product(g_in, g_in)
    g = apex(pr_gr)
    p1, p2 = legs(pr_gr)
    # Todo: we need to restrict these projections to boxtimes

    function pred(g, e, p1, p2)
        (x, y) = p1[:V](src(g, e)), p2[:V](src(g, e))
        (w, z) = p1[:V](tgt(g, e)), p2[:V](tgt(g, e))
        return !(x == z && y == w && x != y)
    end

    #to_rem = filter(e -> pred(g, e, p1, p2), edges(g))
    g_res = Subobject(g, V=vertices(g), E=filter(e -> pred(g, e, p1, p2), edges(g)))
    #g_res = deepcopy(g)
    #rem_edges!(g_res, to_rem)

    return dom(hom(g_res)), hom(g_res) ⋅ p1, hom(g_res) ⋅ p2
end

# Takes a contraction and returns the equalizer along boxtimes
function β(f)
    G = dom(f)
    GbG, p1, p2 = boxtimes(G)

    e = equalizer(p1 ⋅ f, p2 ⋅ f)

    return e
end

function black_edges(g, v1, v2)
    H, f = contract_vertices(g, v1, v2)
    # TODO
    i = hom(closed_neighborhood(g, [v1, v2]))
    N = dom(i)
    println(typeof(N))

    NbN, p1, p2 = boxtimes(N)

    e = equalizer(p1 ⋅ i ⋅ f, p2 ⋅ i ⋅ f)

    b = legs(e)[1]

    return image(b ⋅ p1 ⋅ i ⋅ f)
end


# Tests
G = @acset SymmetricReflexiveGraph begin
    V = 4
    E = 12
    refl = [1, 2, 5, 6]
    src = [1, 2, 1, 2, 3, 4, 3, 4, 1, 2, 1, 4]
    tgt = [1, 2, 2, 1, 3, 4, 1, 2, 3, 4, 4, 1]
    inv = [1, 2, 4, 3, 5, 6, 9, 10, 7, 8, 12, 11]
end

B = black_edges(G, 2, 3)


#H = complete_graph(SymmetricReflexiveGraph, 3)

#f = homomorphisms(G, H)[15]



#H, f = contract_vertices(G, 2, 3)

#GbG, p1, p2 = boxtimes(G)
#e = β(f)
#b = legs(e)[1]
#B = image(b ⋅ p1 ⋅ f)

