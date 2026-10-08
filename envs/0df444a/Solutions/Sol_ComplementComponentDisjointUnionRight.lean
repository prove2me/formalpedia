-- Prove2me | solution 1 for ComplementComponentDisjointUnionRight
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:11:40.452802+00:00
-- url     : https://prove2.me/submissions/64bbc627-21d5-4903-8987-2b228e4dc58f

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData



theorem solution
    (A B C : Set (EuclideanSpace ℝ (Fin 2))) :
    ComplementComponent A C → Disjoint C B →
      ComplementComponent (A ∪ B) C := by
  intro hC hCB
  rcases hC with ⟨hCne, hCA, hCconn, hCmax⟩
  refine ⟨hCne, ?_, hCconn, ?_⟩
  · intro x hxC
    change x ∉ A ∪ B
    intro hxAB
    rcases hxAB with hxA | hxB
    · exact (hCA hxC) hxA
    · exact (Set.disjoint_left.mp hCB) hxC hxB
  · intro D hDne hDAB hDconn hCD
    have hDA : D ⊆ Aᶜ := by
      intro x hxD
      change x ∉ A
      intro hxA
      exact (hDAB hxD) (Or.inl hxA)
    exact hCmax D hDne hDA hDconn hCD
