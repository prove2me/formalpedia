-- Prove2me | solution 1 for CachonPushPull.ShippingCost.retailer_never_worse
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:22:57.761007+00:00
-- url     : https://prove2.me/submissions/987c37a7-93a8-4d6e-acf5-9f3eff256da5

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game



namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

theorem rnw_br_indep (μ : Measure ℝ) (c v τ w₁ w₁' w₂ y q : ℝ)
    (h : IsSupplierBestResponse μ c v τ w₁ w₂ y q) :
    IsSupplierBestResponse μ c v τ w₁' w₂ y q := by
  refine ⟨h.1, fun q' hq' => ?_⟩
  have := h.2 q' hq'
  unfold supplierProfit at *
  linarith

theorem rnw_core (μ : Measure ℝ) (p c v τ w₁ w₂ : ℝ) (hw₁₂ : w₁ ≤ w₂) :
    ∀ y q y₀ q₀ : ℝ, IsOutcome μ p c v τ w₁ w₂ y q → IsOutcome μ p c v τ w₂ w₂ y₀ q₀ →
      retailerProfit μ p v w₂ w₂ y₀ q₀ ≤ retailerProfit μ p v w₁ w₂ y q := by
  intro y q y₀ q₀ h h₀
  have h1 := h.2.2 y₀ q₀ h₀.1 (rnw_br_indep μ c v τ w₂ w₁ w₂ y₀ q₀ h₀.2.1)
  have h2 : 0 ≤ (w₂ - w₁) * y₀ := mul_nonneg (by linarith) h₀.1
  unfold retailerProfit at *
  linarith

end CachonPushPull.ShippingCost

open CachonPushPull.ShippingCost
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₁ w₂ : ℝ) (hw₁₂ : w₁ ≤ w₂) (hw₂p : w₂ < p) :
    ∀ y q y₀ q₀ : ℝ, IsOutcome μ p c v τ w₁ w₂ y q → IsOutcome μ p c v τ w₂ w₂ y₀ q₀ →
      retailerProfit μ p v w₂ w₂ y₀ q₀ ≤ retailerProfit μ p v w₁ w₂ y q := by
  exact rnw_core μ p c v τ w₁ w₂ hw₁₂
