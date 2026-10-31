-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_corrected_ubv_zero_horizon_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:15:07.327154+00:00
-- url     : https://prove2.me/submissions/280b6348-135e-439e-8a12-046718e9ac45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_repaired_boundary_nonneg_all_cap
import Theorems.Thm_AvramDividend_Classical_truncated_zero_horizon_bound_of_initial_jump_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The repaired UBV verification hypotheses genuinely control the full
initial dividend Stieltjes atom, at the zero-time horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hJump0 (ω : Ω) :
      rightLimit D 0 ω - D 0 ω ≤
        w x - w (x - (rightLimit D 0 ω - D 0 ω)) := by
    have h := hjump ω 0 (Or.inl rfl)
    dsimp [riskProcess] at h
    simpa [hs.1 ω, X.X_zero ω] using h
  have hpost (ω : Ω) :
      0 ≤ w (x - (rightLimit D 0 ω - D 0 ω)) := by
    have hstate := capped_postPaymentReserve_initial_state X x C D hD hxc ω
    have hval := avram_wave3_04_repaired_boundary_nonneg_all_cap
      C w hw0 hw_cont hw_smooth hw_grad
      (x + X.X 0 ω - rightLimit D 0 ω) hstate.1 hstate.2
    simpa [hs.1 ω, X.X_zero ω] using hval
  exact truncated_zero_horizon_bound_of_initial_jump_secant
    X q x w D hs hJump0 hpost
