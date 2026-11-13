-- Prove2me | solution 1 for CountingLLL.RandomRAM.product_relative_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:11:49.862203+00:00
-- url     : https://prove2.me/submissions/e87da3c6-077e-4f69-8eb6-48c0d07b9a43

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Relative second moment of an independent product, as used in equation (34). -/
theorem product_relative_second_moment {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0) :
    (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) / (∏ i, ∫ ω, X i ω ∂μ) ^ 2 =
      ∏ i, (1 + variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) := by
  have hprod : (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) = ∏ i, ∫ ω, (X i ω) ^ 2 ∂μ := by
    have h := hind.integral_fun_prod_comp (f := fun (_ : ι) (x : ℝ) => x ^ 2)
      (fun i => (hL2 i).aemeasurable) (fun i => by fun_prop)
    simpa [Finset.prod_pow] using h
  rw [hprod, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [variance_eq_sub (hL2 i)]
  simp only [Pi.pow_apply]
  have hn : (∫ ω, X i ω ∂μ) ^ 2 ≠ 0 := pow_ne_zero 2 (hmean i)
  field_simp [hmean i]
  <;> ring

theorem product_relative_second_moment_le_exp {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0) :
    (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) / (∏ i, ∫ ω, X i ω ∂μ) ^ 2 ≤
      Real.exp (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) := by
  rw [product_relative_second_moment μ X hind hL2 hmean]
  apply Real.prod_one_add_le_exp_sum
  intro i
  exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)

theorem solution {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0) :
    (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) / (∏ i, ∫ ω, X i ω ∂μ) ^ 2 =
      ∏ i, (1 + variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) ∧
    (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) / (∏ i, ∫ ω, X i ω ∂μ) ^ 2 ≤
      Real.exp (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) :=
  ⟨product_relative_second_moment μ X hind hL2 hmean,
    product_relative_second_moment_le_exp μ X hind hL2 hmean⟩
