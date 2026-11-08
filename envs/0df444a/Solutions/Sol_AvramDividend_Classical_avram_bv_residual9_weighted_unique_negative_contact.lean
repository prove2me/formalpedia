-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_weighted_unique_negative_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:25:00.054296+00:00
-- url     : https://prove2.me/submissions/3fea66ad-f6cd-4dd7-a1be-462d3bd31786

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single exceptional contact controls the weighted negative post-value error. -/
theorem solution
    (w post : ℕ → ℝ) (m j : ℕ)
    (hj : j < m + 1)
    (hw : ∀ i, i < m + 1 → w i ≤ 1)
    (hpost : ∀ i, i < m + 1 → i ≠ j → 0 ≤ post (i + 1)) :
    (∑ i ∈ Finset.range (m + 1),
      w i * max (-post (i + 1)) 0) ≤
      max (-post (j + 1)) 0 := by
  have hsum :
      (∑ i ∈ Finset.range (m + 1),
        w i * max (-post (i + 1)) 0) =
        w j * max (-post (j + 1)) 0 := by
    apply Finset.sum_eq_single j
    · intro i hi hne
      have hp : 0 ≤ post (i + 1) :=
        hpost i (Finset.mem_range.mp hi) hne
      have hm : max (-post (i + 1)) 0 = 0 :=
        max_eq_right (neg_nonpos.mpr hp)
      simp [hm]
    · intro hjnot
      exact (hjnot (Finset.mem_range.mpr hj)).elim
  rw [hsum]
  have hzero : 0 ≤ max (-post (j + 1)) 0 := le_max_right _ _
  calc
    w j * max (-post (j + 1)) 0 ≤
        1 * max (-post (j + 1)) 0 :=
      mul_le_mul_of_nonneg_right (hw j hj) hzero
    _ = max (-post (j + 1)) 0 := one_mul _
