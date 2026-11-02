-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_inward_secant_slope_ge_one_all_scales
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:41:36.597664+00:00
-- url     : https://prove2.me/submissions/298ab97f-5a79-4465-a85d-a9babae8aa8b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Without any endpoint derivative, all inward cap secants of the corrected UBV
candidate dominate the rightward slope one used by its cap-linear extension.
This is the sign interface for a separately justified Ito corner approximation.
-/

/-- Every inward cap-corner difference quotient is at least one. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (δ : ℝ) (hδ : 0 < δ) (hδc : δ ≤ c) :
    1 ≤ (w c - w (c - δ)) / δ := by
  have ha : 0 ≤ c - δ := sub_nonneg.mpr hδc
  have hab : c - δ ≤ c := by linarith
  have hSec :=
    avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      (ENNReal.ofReal c) w hw_cont hw_smooth hw_grad
      (c - δ) c ha hab le_rfl
  have hSlope : δ ≤ w c - w (c - δ) := by
    linarith
  exact (le_div_iff₀ hδ).2 (by simpa only [one_mul] using hSlope)
