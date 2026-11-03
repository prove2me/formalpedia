-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:06:25.254081+00:00
-- url     : https://prove2.me/submissions/d2943f34-9dcb-47af-a19e-7f3d175c1552

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At a measurable finite random clock, the original expected
    ENNReal fibre.toReal equals genuine expected signed Stieltjes
    payout on precisely the source stopped payout domain. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hDiv : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫ ω, (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hFibre (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal =
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
    rw [avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
      X x D hDiv ω (τ ω : ℝ) (NNReal.coe_nonneg _) q hq]
    apply ENNReal.toReal_ofReal
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  apply integral_congr_ae
  exact Filter.Eventually.of_forall hFibre
