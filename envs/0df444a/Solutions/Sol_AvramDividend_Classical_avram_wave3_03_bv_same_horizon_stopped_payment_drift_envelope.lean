-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_same_horizon_stopped_payment_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:37:13.848361+00:00
-- url     : https://prove2.me/submissions/66b86598-f717-45cd-8bd9-65e823e942b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightLimit_and_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine BV Lévy drift envelope bounds every stopped Stieltjes
payment through T, including the right atom at T, whenever the controlled
reserve remains solvent immediately to the right of T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (∀ᶠ s in 𝓝[>] T, 0 ≤ riskProcess X x D s ω) →
      (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hmono
  intro hnear
  have hpost : 0 ≤ x + X.X T ω - rightLimit D T ω :=
    (postPaymentReserve_rightLimit_and_nonnegative X x D hD ω T).2 hnear
  have hmono0 :
      (0 : ℝ) * X.drift - X.X 0 ω ≤
        (T : ℝ) * X.drift - X.X T ω :=
    hmono (show (0 : ℝ≥0) ≤ T from zero_le)
  have hX : X.X T ω ≤ (T : ℝ) * X.drift := by
    have hh : 0 ≤ (T : ℝ) * X.drift - X.X T ω := by
      simpa [X.X_zero ω] using hmono0
    linarith
  calc
    _ ≤ ENNReal.ofReal (rightLimit D T ω) :=
      avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
        q hq D hD ω σ T
    _ ≤ ENNReal.ofReal (x + (T : ℝ) * X.drift) :=
      ENNReal.ofReal_le_ofReal (by linarith)