-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_uniform_trunc_signed_budgets_imply_full_signed_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:50:35.20838+00:00
-- url     : https://prove2.me/submissions/323e5836-cd52-4e2d-a9d1-183acae0f022

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Uniform original signed budgets on bounded random truncations
    control the actual original full signed mean at a finite random clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
  have hENN :=
    avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
      X x C D hD q hq τ hτMeas B hBudget
  have hFinite :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤ :=
    lt_of_le_of_lt hENN ENNReal.ofReal_lt_top
  have hEq :=
    avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
      X x C D hD q hq τ hτMeas hFinite
  have hB : 0 ≤ B := by
    have h0 : 0 ≤
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
            Iic ((min (τ ω) (((0 + 1 : ℕ) : ℝ≥0)) : ℝ)),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
      apply integral_nonneg
      intro ω
      apply integral_nonneg
      intro t
      exact (Real.exp_pos (-(q * t))).le
    exact h0.trans (hBudget 0)
  have hMeanNonneg : 0 ≤
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    apply integral_nonneg
    intro ω
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hLe : ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤
      ENNReal.ofReal B := by
    calc
      ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) =
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := hEq.symm
      _ ≤ ENNReal.ofReal B := hENN
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hLe
  simpa only [ENNReal.toReal_ofReal hMeanNonneg,
    ENNReal.toReal_ofReal hB] using hReal
