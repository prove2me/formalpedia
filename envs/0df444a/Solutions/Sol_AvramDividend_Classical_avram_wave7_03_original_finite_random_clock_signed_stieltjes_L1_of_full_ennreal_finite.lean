-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:26:58.637065+00:00
-- url     : https://prove2.me/submissions/efaf2d7a-0401-4303-b84f-0169990b4f2c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_toReal_cash_L1_of_full_ennreal_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite original expected ENNReal payout makes the genuine signed
    stopped Stieltjes reward L1, for an unbounded but finite random clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hFInt : Integrable (fun ω => (F ω).toReal) P := by
    exact avram_wave7_03_original_finite_random_clock_toReal_cash_L1_of_full_ennreal_finite
      X x D hDiv q τ hτMeas hCashFinite
  have hPath (ω : Ω) : F ω = ENNReal.ofReal (g ω) := by
    exact avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
      X x D hDiv ω (τ ω : ℝ) (NNReal.coe_nonneg _) q hq
  have hg (ω : Ω) : 0 ≤ g ω := by
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hEq : (fun ω => (F ω).toReal) =ᵐ[P] g := by
    apply Filter.Eventually.of_forall
    intro ω
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal (hPath ω)
      _ = g ω := ENNReal.toReal_ofReal (hg ω)
  exact hFInt.congr hEq
