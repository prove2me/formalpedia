-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_ruin_bounded_random_clock_real_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:42:06.581207+00:00
-- url     : https://prove2.me/submissions/117ce682-c7f6-431a-8ce9-af8b16f3b2a2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hMass : ∀ᵐ ω ∂P,
      (dividendMeasure D ω)
        (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ)) ≠ ⊤) :
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
  have hFInt : Integrable (fun ω => (F ω).toReal) P := by
    simpa only [F] using
      (avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
        X x C D hD q τ T hτMeas hτBound)
  have hPathEq : F =ᵐ[P] (fun ω => ENNReal.ofReal (g ω)) := by
    filter_upwards [hMass] with ω hω
    simpa only [F, g] using
      (avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq
        X x D hDiv ω (τ ω : ℝ) (NNReal.coe_nonneg _) q hq hω)
  have hNonneg : ∀ ω, 0 ≤ g ω := by
    intro ω
    change 0 ≤ ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hCashEq : (fun ω => (F ω).toReal) =ᵐ[P] g := by
    filter_upwards [hPathEq] with ω hω
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal hω
      _ = g ω := ENNReal.toReal_ofReal (hNonneg ω)
  have hRealInt : Integrable g P := hFInt.congr hCashEq
  change (∫⁻ ω, F ω ∂P) = ENNReal.ofReal (∫ ω, g ω ∂P)
  calc
    (∫⁻ ω, F ω ∂P) = ∫⁻ ω, ENNReal.ofReal (g ω) ∂P :=
      lintegral_congr_ae hPathEq
    _ = ENNReal.ofReal (∫ ω, g ω ∂P) := by
      symm
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        hRealInt (Filter.Eventually.of_forall hNonneg)
