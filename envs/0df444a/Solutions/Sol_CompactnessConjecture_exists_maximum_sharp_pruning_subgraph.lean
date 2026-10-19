-- Prove2me | solution 1 for CompactnessConjecture.exists_maximum_sharp_pruning_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/878f9efb-2e34-482f-88ec-e3e21d7db120

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (base : SimpleGraph V) (originalEdges : ℕ) :
    ∃ H : SimpleGraph V, H ≤ base ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningPotential originalEdges D ≤
          sharpPruningPotential originalEdges H) ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningScore originalEdges D ≤
          sharpPruningScore originalEdges H) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H : SimpleGraph V => H ≤ base)
  have hnonempty : candidates.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [candidates]
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    candidates (sharpPruningScore originalEdges) hnonempty
  refine ⟨H, (Finset.mem_filter.mp hH).2, ?_, ?_⟩
  · intro D hD
    have hscore := hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)
    unfold sharpPruningScore at hscore
    split_ifs at hscore <;> omega
  · intro D hD
    exact hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)
end CompactnessConjecture
