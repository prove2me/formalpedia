-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_vand_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:48.440156+00:00
-- url     : https://prove2.me/submissions/1f24deec-c39e-475a-80e9-ef27a94bd0fe

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds

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
theorem _root_.solution (K : ℕ) (u v : ℕ → ℝ) (hint : ∀ i, i < K → v i < u i ∧ u (i + 1) < v i)
    (hu : ∀ i j, i < j → j < K + 1 → 1 ≤ u i - u j)
    (hv : ∀ i j, i < j → j < K → v j < v i) : vandN v K ≤ vandN u (K + 1) := by
  have h1 : vandN v K ≤ ∏ i ∈ range K, ∏ j ∈ Ico (i + 1) K, (u i - u (j + 1)) := by
    unfold vandN
    apply Finset.prod_le_prod
    · intro i hi
      apply Finset.prod_nonneg
      intro j hj
      simp only [mem_Ico, mem_range] at hi hj
      have := hv i j (by omega) hj.2
      linarith
    · intro i hi
      apply Finset.prod_le_prod
      · intro j hj
        simp only [mem_Ico, mem_range] at hi hj
        have := hv i j (by omega) hj.2
        linarith
      · intro j hj
        simp only [mem_Ico, mem_range] at hi hj
        have h1 := (hint i hi).1
        have h2 := (hint j hj.2).2
        linarith
  refine le_trans h1 ?_
  unfold vandN
  rw [Finset.prod_range_succ]
  simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
  apply Finset.prod_le_prod
  · intro i hi
    apply Finset.prod_nonneg
    intro j hj
    simp only [mem_Ico, mem_range] at hi hj
    have := hu i (j + 1) (by omega) (by omega)
    linarith
  · intro i hi
    simp only [mem_range] at hi
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : i + 1 < K + 1)]
    rw [← Finset.prod_Ico_add' (fun j => u i - u j) (i + 1) K 1]
    have hrow : 0 ≤ ∏ j ∈ Ico (i + 1) K, (u i - u (j + 1)) := by
      apply Finset.prod_nonneg
      intro j hj
      simp only [mem_Ico] at hj
      have := hu i (j + 1) (by omega) (by omega)
      linarith
    have hgap : 1 ≤ u i - u (i + 1) := hu i (i + 1) (by omega) (by omega)
    have : ∏ j ∈ Ico (i + 1) K, (u i - u (j + 1)) ≤
        (u i - u (i + 1)) * ∏ j ∈ Ico (i + 1) K, (u i - u (j + 1)) := by nlinarith
    simpa using this
end Formalism.LogVandermondeBounds.StandardLattice
