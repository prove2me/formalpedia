-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_interior_cutoff_secant_defect_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:02:04.151202+00:00
-- url     : https://prove2.me/submissions/4bfd65c8-583b-432a-be29-ad283f389b8c

import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Uniform cap-corner approximation by strictly interior cutoffs. The slope-one
continuation frozen at b<c differs from the true cap continuation by a
nonnegative amount uniformly bounded by the vanishing cap secant defect.
No left derivative at c, C2 at c, or stochastic local-time assertion is used.
-/

/-- The interior-cutoff slope-one continuation under-approximates the cap
    continuation, with a state-uniform error bounded by the cap secant defect. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (b : ℝ) (hb0 : 0 ≤ b) (hbc : b ≤ c)
    (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ (if y ≤ c then w y else w c + (y - c)) -
      (if y ≤ b then w y else w b + (y - b)) ∧
    (if y ≤ c then w y else w c + (y - c)) -
      (if y ≤ b then w y else w b + (y - b)) ≤
      (w c - w b) - (c - b) := by
  have hSecBC :=
    avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      (ENNReal.ofReal c) w hw_cont hw_smooth hw_grad
      b c hb0 hbc le_rfl
  by_cases hyb : y ≤ b
  · have hyc : y ≤ c := le_trans hyb hbc
    simp only [if_pos hyc, if_pos hyb]
    constructor <;> linarith
  · have hby : b ≤ y := le_of_lt (lt_of_not_ge hyb)
    by_cases hyc : y ≤ c
    · have hSecBY :=
        avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
          (ENNReal.ofReal c) w hw_cont hw_smooth hw_grad
          b y hb0 hby (ENNReal.ofReal_le_ofReal hyc)
      have hSecYC :=
        avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
          (ENNReal.ofReal c) w hw_cont hw_smooth hw_grad
          y c hy hyc le_rfl
      simp only [if_pos hyc, if_neg hyb]
      constructor <;> linarith
    · simp only [if_neg hyc, if_neg hyb]
      constructor <;> linarith
