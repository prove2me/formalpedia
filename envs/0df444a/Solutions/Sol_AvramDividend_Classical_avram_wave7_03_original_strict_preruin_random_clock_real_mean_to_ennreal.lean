-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:13:28.307392+00:00
-- url     : https://prove2.me/submissions/e53cc400-ed04-4cc2-bfb5-13d5daff3cf4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact original-measure expected Stieltjes cash conversion at a random
    zero-or-strict-pre-ruin clock, under the necessary real L¹ assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (τ : Ω → ℝ≥0)
    (hPre : ∀ᵐ ω ∂P,
      τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (hRealInt : Integrable (fun ω =>
      ∫ t in Icc (0 : ℝ) (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in Icc (0 : ℝ) (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let g : Ω → ℝ := fun ω =>
    ∫ t in Icc (0 : ℝ) (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)
  have hEq : F =ᵐ[P] (fun ω => ENNReal.ofReal (g ω)) := by
    filter_upwards [hPre] with ω hω
    simpa only [F, g] using
      (avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
        X x D hD ω (τ ω) hω q hq)
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ g ω := by
    apply Filter.Eventually.of_forall
    intro ω
    change 0 ≤ ∫ t in Icc (0 : ℝ) (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hCash :
      (∫⁻ ω, F ω ∂P) =
      ENNReal.ofReal (∫ ω, g ω ∂P) := by
    calc
      (∫⁻ ω, F ω ∂P) =
          ∫⁻ ω, ENNReal.ofReal (g ω) ∂P :=
            lintegral_congr_ae hEq
      _ = ENNReal.ofReal (∫ ω, g ω ∂P) := by
        symm
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (by simpa only [g] using hRealInt) hNonneg
  change (∫⁻ ω, F ω ∂P) =
      ENNReal.ofReal (∫ ω, g ω ∂P)
  exact hCash
