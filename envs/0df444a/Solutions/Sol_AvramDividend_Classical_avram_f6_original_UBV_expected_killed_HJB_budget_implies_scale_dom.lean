-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_expected_killed_HJB_budget_implies_scale_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:07:07.784633+00:00
-- url     : https://prove2.me/submissions/5c0b3cf2-bd98-423d-af56-3169a7ec4373

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_true_discounted_first_exit_scale_ratio
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w W : ℝ → ℝ) (hw1 : 0 ≤ w 1)
    (hW : IsScaleFunction X q W)
    (hExit : ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectation X q b 1).toReal ≤ w 1) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ b : ℝ, 1 ≤ b → w b ≤ A * W b := by
  have hW1 : 0 < W 1 :=
    scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hBV 1 (by norm_num)
  let A : ℝ := w 1 / W 1
  have hA : 0 ≤ A := div_nonneg hw1 hW1.le
  refine ⟨A, hA, ?_⟩
  intro b hb
  have hWb : 0 < W b :=
    scaleFunction_strict_pos_of_unbounded_variation
      X q W hW hBV b (by linarith)
  have hratio :=
    avram_f6_original_UBV_true_discounted_first_exit_scale_ratio
      X hX hBV q hq W hW b hb
  have hratioPos : 0 ≤ W 1 / W b := div_nonneg hW1.le hWb.le
  have hExit' : w b * (W 1 / W b) ≤ w 1 := by
    simpa [hratio, ENNReal.toReal_ofReal hratioPos] using hExit b hb
  have hScaled := mul_le_mul_of_nonneg_right hExit' hWb.le
  have hCancel : (w b * (W 1 / W b)) * W b = w b * W 1 := by
    field_simp
  rw [hCancel] at hScaled
  calc
    w b ≤ (w 1 * W b) / W 1 := (le_div_iff₀ hW1).2 hScaled
    _ = A * W b := by dsimp [A]; ring
