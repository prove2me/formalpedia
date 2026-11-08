-- Prove2me | solution 1 for BidPriceControl.Asymptotic.explicit_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:00:54.992333+00:00
-- url     : https://prove2.me/submissions/50238671-c3e1-482d-8964-20980e2b35e1

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model
import Theorems.Thm_BidPriceControl_Asymptotic_coupling_bound
import Theorems.Thm_BidPriceControl_Asymptotic_relaxed_value_scaling
import Theorems.Thm_BidPriceControl_Asymptotic_bid_price_revenue_identity
import Theorems.Thm_BidPriceControl_Asymptotic_overflow_bound
import Theorems.Thm_BidPriceControl_Asymptotic_seats_mean_variance

open MeasureTheory ProbabilityTheory

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (C : ℝ) (hC : ∀ t ∈ Finset.Icc 1 k, ∀ᵐ r ∂(F t), ∀ j, r j ≤ C)
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) :
    (θ : ℝ) * relaxedValue A F k x μstar
        - C / 2 * Real.sqrt (θ : ℝ) *
          ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 k, ∑ j, indicatorVar A F μstar i t j)
      ≤ heuristicValue A (scaledLaw F θ) (θ * k) (θ • x) μstar := by
  have hcb := coupling_bound A F k x hF C hC μstar hmin θ hθ
  have hsc := (relaxed_value_scaling A F k x θ hθ).1 μstar
  have hbp := bid_price_revenue_identity A F k x hF μstar hmin θ hθ
  -- the scaled relaxed value
  have hS1 : (∑ t ∈ Finset.Icc 1 (θ * k), ∑ j,
        ∫ r, max (r j - bidSum A μstar j) 0 ∂(scaledLaw F θ t))
      + (θ : ℝ) * ∑ i, μstar i * (x i : ℝ) = (θ : ℝ) * relaxedValue A F k x μstar := by
    rw [← hsc]
    unfold relaxedValue
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
    ring
  set P := pathMeasure (scaledLaw F θ) (θ * k)
  set E : Fin m → ℝ := fun i =>
    ∫ ω, max (seatsCounted A μstar i ω - (θ : ℝ) * (x i : ℝ)) 0 ∂P with hE
  set W : Fin m → ℝ := fun i => ∑ t ∈ Finset.Icc 1 k, ∑ j, indicatorVar A F μstar i t j with hW
  have hE0 : ∀ i, 0 ≤ E i := fun i => integral_nonneg fun ω => le_max_right _ _
  have hθr : (0 : ℝ) ≤ θ := Nat.cast_nonneg θ
  -- E_i ≤ √θ √W_i / 2
  have hEW : ∀ i, E i ≤ Real.sqrt θ * Real.sqrt (W i) / 2 := by
    intro i
    have h1 := overflow_bound A F k x hF μstar hmin θ hθ i
    have h2 := (seats_mean_variance A F k x hF μstar hmin θ hθ i).2
    calc E i ≤ _ := h1
      _ ≤ Real.sqrt (θ * W i) / 2 := by
          gcongr
      _ = Real.sqrt θ * Real.sqrt (W i) / 2 := by rw [Real.sqrt_mul hθr]
  have key : (θ : ℝ) * relaxedValue A F k x μstar - C * ∑ i, E i
      ≤ heuristicValue A (scaledLaw F θ) (θ * k) (θ • x) μstar := by
    rw [← hS1, ← hbp]; exact hcb
  by_cases hC0 : 0 ≤ C
  · have : C * ∑ i, E i ≤ C / 2 * Real.sqrt θ * ∑ i, Real.sqrt (W i) := by
      calc C * ∑ i, E i ≤ C * ∑ i, Real.sqrt θ * Real.sqrt (W i) / 2 := by
            gcongr with i; exact hEW i
        _ = C / 2 * Real.sqrt θ * ∑ i, Real.sqrt (W i) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i _; ring
    linarith
  · push Not at hC0
    have hW0 : ∀ i, W i = 0 := by
      intro i
      simp only [hW]
      apply Finset.sum_eq_zero
      intro t ht
      apply Finset.sum_eq_zero
      intro j _
      exfalso
      haveI := (hF t ht).isProbabilityMeasure
      have hae : ∀ᵐ r ∂(F t), False :=
        ((hC t ht).and (hF t ht).ae_inS).mono fun r h => by
          have := h.2.1 j
          have := h.1 j
          linarith
      obtain ⟨_, h⟩ := hae.exists
      exact h
    have hsum0 : ∑ i, Real.sqrt (W i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hW0 i, Real.sqrt_zero]
    have : 0 ≤ ∑ i, E i := Finset.sum_nonneg fun i _ => hE0 i
    have : C * ∑ i, E i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0.le this
    simp only [hW] at hsum0
    rw [hsum0, mul_zero, sub_zero]
    linarith
