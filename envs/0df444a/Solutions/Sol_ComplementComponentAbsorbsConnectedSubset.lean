-- Prove2me | solution 1 for ComplementComponentAbsorbsConnectedSubset
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:11:39.794158+00:00
-- url     : https://prove2.me/submissions/89f5ec9c-4752-47ee-8c92-66b34d2a7a2d

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

theorem solution
    (K C T : Set (EuclideanSpace ℝ (Fin 2))) :
    ComplementComponent K C →
      T.Nonempty → T ⊆ Kᶜ → IsConnected T →
        (C ∩ T).Nonempty → T ⊆ C := by
  intro hC hTne hTK hTconn hmeet
  rcases hC with ⟨_hCne, hCK, hCconn, hCmax⟩
  have hUnionNonempty : (C ∪ T).Nonempty := hTne.mono (by
    intro x hx
    exact Or.inr hx)
  have hUnionSubset : C ∪ T ⊆ Kᶜ := by
    intro x hx
    rcases hx with hxC | hxT
    · exact hCK hxC
    · exact hTK hxT
  have hUnionConnected : IsConnected (C ∪ T) :=
    IsConnected.union hmeet hCconn hTconn
  have hCUnion : C ⊆ C ∪ T := by
    intro x hx
    exact Or.inl hx
  have hUnionC : C ∪ T ⊆ C :=
    hCmax (C ∪ T) hUnionNonempty hUnionSubset hUnionConnected hCUnion
  intro x hxT
  exact hUnionC (Or.inr hxT)
