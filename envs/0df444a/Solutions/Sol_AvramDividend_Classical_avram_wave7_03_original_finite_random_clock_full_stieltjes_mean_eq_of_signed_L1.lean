-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_full_stieltjes_mean_eq_of_signed_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:57:12.426163+00:00
-- url     : https://prove2.me/submissions/d15a0063-16f8-4d39-a822-3c77a15b6e63

import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

/-- The genuine signed full Stieltjes reward L1 hypothesis directly
    converts its original expected cash into the double ENNReal integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hSignedL1 : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hGInt : Integrable g P := hSignedL1
  have hg (ω : Ω) : 0 ≤ g ω := by
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hPath (ω : Ω) : F ω = ENNReal.ofReal (g ω) := by
    exact avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
      X x D hDiv ω (τ ω : ℝ) (NNReal.coe_nonneg _) q hq
  change (∫⁻ ω, F ω ∂P) = ENNReal.ofReal (∫ ω, g ω ∂P)
  calc
    (∫⁻ ω, F ω ∂P) = (∫⁻ ω, ENNReal.ofReal (g ω) ∂P) := by
      apply lintegral_congr
      intro ω
      exact hPath ω
    _ = ENNReal.ofReal (∫ ω, g ω ∂P) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        hGInt (Filter.Eventually.of_forall hg)).symm
