-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_ubv_original_postpayment_nonnegative_affine_terminal_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:34:20.345454+00:00
-- url     : https://prove2.me/submissions/72f313eb-3b4f-444a-8802-81ac30758d31

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! When the actual postpayment value is nonnegative, its original
    zero-boundary closed secant supplies the full w(0)+reserve floor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hy : 0 ≤ x + X.X t ω - rightLimit D t ω) :
    w 0 + (x + X.X t ω - rightLimit D t ω) ≤
      w (x + X.X t ω - rightLimit D t ω) := by
  let y : ℝ := x + X.X t ω - rightLimit D t ω
  have hcap : ENNReal.ofReal y ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
  have hsec := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
    C w hw_cont hw_smooth hw_grad 0 y (le_refl (0 : ℝ)) hy hcap
  dsimp only [y] at *
  linarith
end
