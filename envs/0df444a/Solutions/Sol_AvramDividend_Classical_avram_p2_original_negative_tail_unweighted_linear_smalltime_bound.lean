-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_negative_tail_unweighted_linear_smalltime_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:40:41.460908+00:00
-- url     : https://prove2.me/submissions/74166122-58f6-4d6a-9f3c-573527ef5612

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_negative_tail_weighted_linear_smalltime_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- On the original process, separated negative increments have probability O(h).
This removes the strictly positive fourth-exponential weighting by genuine ENNReal division. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
          ENNReal.ofReal (C * h) := by
  have hExp : Real.exp (-ε) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hWeight : 0 < (1 - Real.exp (-ε)) ^ 4 :=
    pow_pos (by linarith) _
  obtain ⟨C, hCpos, hRate⟩ :=
    avram_p2_original_negative_tail_weighted_linear_smalltime_bound X ε hε
  refine ⟨C / ((1 - Real.exp (-ε)) ^ 4), div_pos hCpos hWeight, ?_⟩
  filter_upwards [hRate] with h hBound
  have hWNonzero :
      ENNReal.ofReal ((1 - Real.exp (-ε)) ^ 4) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hWeight
  have hWFinite :
      ENNReal.ofReal ((1 - Real.exp (-ε)) ^ 4) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hDiv :
      P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
        ENNReal.ofReal (C * h) /
          ENNReal.ofReal ((1 - Real.exp (-ε)) ^ 4) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hWNonzero) (Or.inl hWFinite)).mpr
      (by simpa [mul_comm] using hBound)
  calc
    P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
        ENNReal.ofReal (C * h) /
          ENNReal.ofReal ((1 - Real.exp (-ε)) ^ 4) := hDiv
    _ = ENNReal.ofReal ((C * h) / ((1 - Real.exp (-ε)) ^ 4)) :=
      (ENNReal.ofReal_div_of_pos hWeight).symm
    _ = ENNReal.ofReal ((C / ((1 - Real.exp (-ε)) ^ 4)) * h) := by
      congr 1
      ring
