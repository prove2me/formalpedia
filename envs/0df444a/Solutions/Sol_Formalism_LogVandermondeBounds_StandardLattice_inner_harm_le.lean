-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.inner_harm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:37:41.167808+00:00
-- url     : https://prove2.me/submissions/cc3b07e5-38f9-4bdb-a17a-4c07c75f4ecc

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution {N : ℕ} (a : Fin N) :
    ∑ b ∈ univ.filter (fun b => a < b), (1 : ℝ) / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) ≤
      ∑ i ∈ range N, (1 : ℝ) / ((i : ℝ) + 1) := by
  rw [← Finset.sum_image (f := fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1))
    (g := fun b : Fin N => b.val - a.val - 1)]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨b, _, rfl⟩ := hi
      simp only [Finset.mem_range]; omega
    · intro i _ _; positivity
  · intro b hb c hc hbc
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb hc
    have hb' : a.val < b.val := hb
    have hc' : a.val < c.val := hc
    simp only at hbc
    exact Fin.ext (by omega)
end Formalism.LogVandermondeBounds.StandardLattice
