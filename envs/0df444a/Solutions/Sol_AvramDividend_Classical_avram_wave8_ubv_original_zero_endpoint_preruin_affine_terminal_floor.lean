-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_ubv_original_zero_endpoint_preruin_affine_terminal_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:19:01.568118+00:00
-- url     : https://prove2.me/submissions/321ca202-38e3-4c36-a740-38be272ae151

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Source pre-ruin reserve enjoys the closed affine floor
    w(U) >= w(0)+U, with no derivative or smoothness at reserve zero. -/
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
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    w 0 + riskProcess X x D t ω ≤
      w (riskProcess X x D t ω) := by
  let y : ℝ := riskProcess X x D t ω
  have hy : 0 ≤ y :=
    riskProcess_nonnegative_strictly_before_ruin X x D ω t ht
  have hcap : ENNReal.ofReal y ≤ C :=
    admissibleLe_riskProcess_le_cap_all_times X x C D hD hxc ω t
  have hsec := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
    C w hw_cont hw_smooth hw_grad 0 y (le_refl (0 : ℝ)) hy hcap
  dsimp only [y] at *
  linarith
end
