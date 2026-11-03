-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_bv_bounded_strict_random_clock_real_ennreal_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:19:13.521189+00:00
-- url     : https://prove2.me/submissions/6593ee02-ff0e-4d9b-a2c6-6dabaa8f9646

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original BV random-clock cash is L¹ in its real Stieltjes form, and
    its mean embeds as the original complete double-ENNReal payout. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
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
      (avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
        X hX hBV x hx C hxc D hD q hq T τ hτBound hτMeas)
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
