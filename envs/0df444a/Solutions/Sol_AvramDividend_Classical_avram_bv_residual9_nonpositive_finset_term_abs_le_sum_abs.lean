-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_nonpositive_finset_term_abs_le_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:40:02.806127+00:00
-- url     : https://prove2.me/submissions/a7ba5ed2-52ce-4f1d-ad80-e091f34d769b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- Every nonpositive finite summand is dominated in magnitude by the sum. -/
theorem solution
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ)
    (hneg : ∀ i ∈ s, f i ≤ 0) :
    ∀ i ∈ s, |f i| ≤ |∑ j ∈ s, f j| := by
  classical
  intro i hi
  have hfi : f i ≤ 0 := hneg i hi
  have hsum : (∑ j ∈ s, f j) ≤ 0 := Finset.sum_nonpos hneg
  have hle : (∑ j ∈ s, f j) ≤ f i := by
    calc
      (∑ j ∈ s, f j) ≤ ∑ j ∈ s, (if j = i then f j else 0) := by
        apply Finset.sum_le_sum
        intro j hj
        split_ifs with hij
        · exact le_rfl
        · exact hneg j hj
      _ = f i := by simp [hi]
  rw [abs_of_nonpos hfi, abs_of_nonpos hsum]
  linarith
