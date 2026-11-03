-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_allvariation_bounded_strict_random_clock_real_ennreal_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:24:58.285952+00:00
-- url     : https://prove2.me/submissions/975529b1-cf16-4757-884a-4d06084f2ad8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact original bounded random-clock real Stieltjes mean conversion,
    uniformly across bounded and unbounded Lévy variation. -/
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
    (hPre : ∀ᵐ ω ∂P,
      τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in Icc (0 : ℝ) (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in Icc (0 : ℝ) (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hFInt : Integrable (fun ω => (F ω).toReal) P := by
    simpa only [F] using
      (avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
        X x C D hD q τ T hτMeas hτBound)
  have hCashEq : (fun ω => (F ω).toReal) =ᵐ[P] g := by
    filter_upwards [hPre] with ω hω
    have hPath : F ω = ENNReal.ofReal (g ω) := by
      simpa only [F, g] using
        (avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
          X x D hDiv ω (τ ω) hω q hq)
    have hg : 0 ≤ g ω := by
      change 0 ≤ ∫ t in Icc (0 : ℝ) (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)
      apply integral_nonneg
      intro t
      exact (Real.exp_pos (-(q * t))).le
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal hPath
      _ = g ω := ENNReal.toReal_ofReal hg
  have hRealInt : Integrable g P := hFInt.congr hCashEq
  exact avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal
    X x D hDiv q hq τ hPre (by simpa only [g] using hRealInt)
