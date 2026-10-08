-- Prove2me | solution 1 for ConnectedSubsetContainedInUniqueComplementComponent
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:11:41.025573+00:00
-- url     : https://prove2.me/submissions/b5933c9f-34b5-4fb5-a9c3-6e1c99fed410

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
    (K T : Set (EuclideanSpace ℝ (Fin 2)))
    (hTne : T.Nonempty) (hTK : T ⊆ Kᶜ) (hTconn : IsConnected T) :
    ∃! C : Set (EuclideanSpace ℝ (Fin 2)), ComplementComponent K C ∧ T ⊆ C := by
  rcases hTne with ⟨x, hxT⟩
  have hxK : x ∈ Kᶜ := hTK hxT
  let C₀ : Set (EuclideanSpace ℝ (Fin 2)) := connectedComponentIn Kᶜ x
  have hTC₀ : T ⊆ C₀ :=
    hTconn.2.subset_connectedComponentIn hxT hTK
  have hxC₀ : x ∈ C₀ := mem_connectedComponentIn hxK
  have hC₀comp : ComplementComponent K C₀ := by
    refine ⟨⟨x, hxC₀⟩, connectedComponentIn_subset Kᶜ x, ?_, ?_⟩
    · exact (isConnected_connectedComponentIn_iff).2 hxK
    · intro C hCne hCK hCconn hC₀C
      have hxC : x ∈ C := hC₀C hxC₀
      exact hCconn.2.subset_connectedComponentIn hxC hCK
  refine ⟨C₀, ⟨hC₀comp, hTC₀⟩, ?_⟩
  intro C hC
  rcases hC with ⟨hCcomp, hTC⟩
  rcases hCcomp with ⟨hCne, hCK, hCconn, hCmax⟩
  have hxC : x ∈ C := hTC hxT
  have hC_subset_C₀ : C ⊆ C₀ :=
    hCconn.2.subset_connectedComponentIn hxC hCK
  have hC₀_subset_C : C₀ ⊆ C := by
    exact hCmax C₀ ⟨x, hxC₀⟩ (connectedComponentIn_subset Kᶜ x)
      ((isConnected_connectedComponentIn_iff).2 hxK) hC_subset_C₀
  exact le_antisymm hC_subset_C₀ hC₀_subset_C
