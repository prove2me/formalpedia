-- Prove2me | solution 1 for EdmondsPolytope.edmonds_perfect_matching_polytope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:39:43.854274+00:00
-- url     : https://prove2.me/submissions/e0613a4b-4ac2-4328-8e39-e24711afa5b3

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Definitions.Def_EdmondsPolytope_Solution
public import Theorems.Thm_MatchingPolytope_edmonds_perfect_matching_polytope


set_option autoImplicit true
@[expose] public section
public section
open EdmondsPolytope
namespace EdmondsPolytope
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (perfectMatchingVectors G) = edmondsPolytope G :=
  MatchingPolytope.edmonds_perfect_matching_polytope G
end EdmondsPolytope
