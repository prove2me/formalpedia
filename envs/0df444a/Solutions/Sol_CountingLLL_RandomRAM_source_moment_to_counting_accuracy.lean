-- Prove2me | solution 1 for CountingLLL.RandomRAM.source_moment_to_counting_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:23:32.425989+00:00
-- url     : https://prove2.me/submissions/91fc8a15-f273-4453-b941-54cbfb3b0c23

import Theorems.Thm_CountingLLL_RandomRAM_marginal_variance_budget
import Theorems.Thm_CountingLLL_RandomRAM_product_estimator_cutoff_accuracy

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- #442 §5.3 accuracy and truncation from the stated marginal bounds. -/
theorem solution {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (r : ι → ℝ)
    (a p D L ε : ℝ)
    (ha : 0 < a) (hp : 0 ≤ p) (hD : 1 ≤ D) (hL : 0 < L) (he : 0 < ε) (he1 : ε ≤ 1)
    (hcondition : 4 * Real.exp 1 * p * (D + 1) ^ 2 ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr : ∀ i, r i ≤ (6 / 5) * p)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 1 - r i)
    (hvar : ∀ i, variance (X i) μ ≤ 3 * p / L)
    (hLbound : 8 * (Fintype.card ι : ℝ) ≤ L * (D + 1) ^ 2 * ε ^ 2)
    (f g : Ω → ℝ≥0∞) (Bf Bg : ℝ≥0∞)
    (hBf0 : Bf ≠ 0) (hBg0 : Bg ≠ 0) (hBft : Bf ≠ ⊤) (hBgt : Bg ≠ ⊤)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ Bf) (hEg : ∫⁻ ω, g ω ∂μ ≤ Bg) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω |
      ((1 - ε) * (a * (∏ i, (1 - r i))) ≤ a * (∏ i, X i ω) ∧
      a * (∏ i, X i ω) ≤ (1 + ε) * (a * (∏ i, (1 - r i)))) ∧
      f ω < 16 * Bf ∧ g ω < 16 * Bg} := by
  have hcoef : (10 : ℝ) ≤ 4 * Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hnonneg : 0 ≤ p * (D + 1) ^ 2 := mul_nonneg hp (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hcoef hnonneg
  have hlll : p * (D + 1) ^ 2 ≤ 1 / 10 := by nlinarith
  have hD2 : (4 : ℝ) ≤ (D + 1) ^ 2 := by nlinarith
  have hp4 := mul_le_mul_of_nonneg_left hD2 hp
  have hp_bound : p ≤ 1 / 40 := by nlinarith
  have hpos : ∀ i, 0 < 1 - r i := by
    intro i
    have := hr i
    nlinarith
  have hm : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0 := fun i => by rw [hmean]; linarith [hpos i]
  have hZ : 0 < ∏ i, ∫ ω, X i ω ∂μ := by
    apply Finset.prod_pos
    intro i hi
    rw [hmean]
    exact hpos i
  have hb := CountingLLL.RandomRAM.marginal_variance_budget r (fun i => variance (X i) μ)
    p D L ε hp hD hL he hcondition hr0 hr (fun i => variance_nonneg _ _) hvar hLbound
  have hbudget : (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) ≤ ε ^ 2 / 20 := by
    simpa only [hmean] using hb
  have h := CountingLLL.RandomRAM.product_estimator_cutoff_accuracy μ X a ε ha hind hL2
    hm hZ he he1 hbudget f g Bf Bg hBf0 hBg0 hBft hBgt hf hg hEf hEg
  simpa only [hmean] using h
