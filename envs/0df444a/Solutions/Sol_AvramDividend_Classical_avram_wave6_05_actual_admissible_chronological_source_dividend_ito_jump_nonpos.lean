-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_admissible_chronological_source_dividend_ito_jump_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:51:50.84621+00:00
-- url     : https://prove2.me/submissions/da06f76a-7cba-46d9-a306-4c7dfc6445d6

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_positive_time_original_dividend_jump_w_drop
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_chronological_ito_jump_correction

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- At a simultaneous original source jump and chronological right payment,
the nonlinear Ito correction splits with a nonpositive dividend cash residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hPre : (t : ℝ≥0∞) < ruinTime X x D ω) :
    let before : ℝ :=
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω
    let afterSource : ℝ := x + X.X t ω - D t ω
    let afterPayment : ℝ := x + X.X t ω - rightLimit D t ω
    let sourceJump : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let paymentAtom : ℝ := rightLimit D t ω - D t ω
    (w afterPayment - w before -
        deriv w before * (sourceJump - paymentAtom) =
      (w afterSource - w before - deriv w before * sourceJump) +
        (w afterPayment - w afterSource + deriv w before * paymentAtom)) ∧
      w afterPayment - w afterSource + paymentAtom ≤ 0 := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hDrop := avram_wave6_05_positive_time_original_dividend_jump_w_drop
    X x C hC w hw_cont hw_smooth hw_grad D hD ω t ht hPre
  have hPay :
      (x + X.X t ω - D t ω) -
        (rightLimit D t ω - D t ω) =
      x + X.X t ω - rightLimit D t ω := by
    ring
  have hJump :
      rightLimit D t ω - D t ω ≤
        w (x + X.X t ω - D t ω) -
          w (x + X.X t ω - rightLimit D t ω) := by
    simpa only [riskProcess, hPay] using hDrop
  exact avram_wave4_04b_chronological_ito_jump_correction
    X x D hStrategy w ω t ht hJump
