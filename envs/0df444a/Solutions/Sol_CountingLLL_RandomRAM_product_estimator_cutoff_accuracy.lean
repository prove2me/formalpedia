-- Prove2me | solution 1 for CountingLLL.RandomRAM.product_estimator_cutoff_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:21:01.879624+00:00
-- url     : https://prove2.me/submissions/e7c55115-8707-432d-8244-149a7e334a22

import Theorems.Thm_CountingLLL_RandomRAM_product_estimator_accuracy
import Theorems.Thm_CountingLLL_RandomRAM_truncation_success_bounds

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Equation (34), followed by the two-cost cutoff in #442, §5.3. -/
theorem solution {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (a ε : ℝ)
    (ha : 0 < a) (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0)
    (hZ : 0 < ∏ i, ∫ ω, X i ω ∂μ)
    (he0 : 0 < ε) (he1 : ε ≤ 1)
    (hbudget : (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) ≤ ε ^ 2 / 20)
    (f g : Ω → ℝ≥0∞) (Bf Bg : ℝ≥0∞)
    (hBf0 : Bf ≠ 0) (hBg0 : Bg ≠ 0) (hBft : Bf ≠ ⊤) (hBgt : Bg ≠ ⊤)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ Bf) (hEg : ∫⁻ ω, g ω ∂μ ≤ Bg) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω |
      ((1 - ε) * (a * (∏ i, ∫ ω, X i ω ∂μ)) ≤ a * (∏ i, X i ω) ∧
      a * (∏ i, X i ω) ≤ (1 + ε) * (a * (∏ i, ∫ ω, X i ω ∂μ))) ∧
      f ω < 16 * Bf ∧ g ω < 16 * Bg} := by
  let G : Set Ω := {ω |
    (1 - ε) * (a * (∏ i, ∫ ω, X i ω ∂μ)) ≤ a * (∏ i, X i ω) ∧
    a * (∏ i, X i ω) ≤ (1 + ε) * (a * (∏ i, ∫ ω, X i ω ∂μ))}
  have hg0 : (15 / 16 : ℝ≥0∞) ≤ μ G :=
    CountingLLL.RandomRAM.product_estimator_accuracy μ X a ε ha hind hL2 hmean hZ he0 he1 hbudget
  exact CountingLLL.RandomRAM.truncation_success_bounds μ G f g Bf Bg
    hBf0 hBg0 hBft hBgt hf hg hEf hEg hg0
