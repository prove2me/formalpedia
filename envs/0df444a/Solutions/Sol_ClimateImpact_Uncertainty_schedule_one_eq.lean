-- Prove2me | solution 1 for ClimateImpact.Uncertainty.schedule_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:19:19.136706+00:00
-- url     : https://prove2.me/submissions/2e1adbdd-50d5-43c3-b10f-2aafba8e1f8d

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint

set_option autoImplicit false
open Matrix ClimateImpact.Uncertainty

theorem solution {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∀ i, schedule ρ T t α κ κc c 1 i = ClimateImpact.Interaction.noInteractionRate ρ T α κ κc (c i) t) ∧
    α * gStar S γr ρ T t α κ κc κ₀ c 1 =
      ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 := by
  have h1 : ∀ i, schedule ρ T t α κ κc c 1 i =
      ClimateImpact.Interaction.noInteractionRate ρ T α κ κc (c i) t := by
    intro i
    unfold schedule ClimateImpact.Interaction.noInteractionRate
    congr 1
    ring
  refine ⟨h1, ?_⟩
  have h2 : ext0 ρ T t α κ κc κ₀ c = extAt ρ T t α κ κc κ₀ c 1 := by
    funext i
    simp only [ext0, extAt, h1]
  unfold gStar greenPortfolio quadForm
  rw [h2]
  generalize extAt ρ T t α κ κc κ₀ c 1 = θ
  simp only [dotProduct]
  generalize S⁻¹ *ᵥ θ = w
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
