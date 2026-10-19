-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_common_neighbor_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/e6d068e5-299b-4f34-a5fd-056b800c7f0a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLine_eq_of_points

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {u v : QuadrangleVertex K} (huv : u ≠ v)
    {w z : QuadrangleVertex K}
    (huw : (symplecticQuadrangle K).Adj u w)
    (hvw : (symplecticQuadrangle K).Adj v w)
    (huz : (symplecticQuadrangle K).Adj u z)
    (hvz : (symplecticQuadrangle K).Adj v z) : w = z := by
  rcases u with p | L <;>
    rcases v with q | M <;>
    rcases w with r | R <;>
    rcases z with s | S <;>
    simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at huw hvw huz hvz
  · apply congrArg Sum.inr
    apply symplecticLine_eq_of_points K
      (fun hpq => huv (congrArg Sum.inl hpq))
    · exact huw
    · exact hvw
    · exact huz
    · exact hvz
  · apply congrArg Sum.inl
    by_contra hrs
    have hlines : L = M := symplecticLine_eq_of_points K hrs
      huw huz hvw hvz
    exact huv (congrArg Sum.inr hlines)
end CompactnessConjecture
