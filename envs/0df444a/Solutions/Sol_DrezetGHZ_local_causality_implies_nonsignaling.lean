-- Prove2me | solution 1 for DrezetGHZ.local_causality_implies_nonsignaling
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:24:40.519569+00:00
-- url     : https://prove2.me/submissions/72d578bf-5ff3-4fb3-8ed8-ec1d9e8a7d28

import Definitions.Def_DrezetGHZ_Models
set_option autoImplicit false
open DrezetGHZ MeasureTheory

private theorem response_le_one {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ) (j : Fin 3) (lam : Λ) (n : Setting) (α : ℤˣ) :
    M.P j lam n α ≤ 1 := by
  rw [← M.P_sum_one j lam n]
  exact Finset.single_le_sum (fun a _ => M.P_nonneg j lam n a) (Finset.mem_univ α)

private theorem response_product_integrable {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ) (n₁ n₂ n₃ : Setting) (α β γ : ℤˣ) :
    Integrable (fun lam => M.P 0 lam n₁ α * M.P 1 lam n₂ β * M.P 2 lam n₃ γ) M.ρ := by
  letI := M.isProbabilityMeasure
  apply (integrable_const (1 : ℝ)).mono'
    (((M.P_measurable 0 n₁ α).mul (M.P_measurable 1 n₂ β)).mul
      (M.P_measurable 2 n₃ γ)).aestronglyMeasurable
  filter_upwards [] with lam
  change ‖M.P 0 lam n₁ α * M.P 1 lam n₂ β * M.P 2 lam n₃ γ‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (mul_nonneg (M.P_nonneg 0 lam n₁ α) (M.P_nonneg 1 lam n₂ β))
    (M.P_nonneg 2 lam n₃ γ))]
  exact mul_le_one₀ (mul_le_one₀ (response_le_one M 0 lam n₁ α)
    (M.P_nonneg 1 lam n₂ β) (response_le_one M 1 lam n₂ β))
    (M.P_nonneg 2 lam n₃ γ) (response_le_one M 2 lam n₃ γ)

private theorem marginal_formula {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ) (n₁ n₂ n₃ : Setting) (α : ℤˣ) :
    ∑ β, ∑ γ, M.predict n₁ n₂ n₃ α β γ = ∫ lam, M.P 0 lam n₁ α ∂M.ρ := by
  simp only [LocalCausalModel.predict]
  simp_rw [← integral_finsetSum Finset.univ (fun γ _ =>
    response_product_integrable M n₁ n₂ n₃ α _ γ)]
  rw [← integral_finsetSum Finset.univ (fun β _ =>
    integrable_finsetSum _ (fun γ _ => response_product_integrable M n₁ n₂ n₃ α β γ))]
  congr 1
  funext lam
  simp_rw [← Finset.mul_sum, M.P_sum_one, mul_one]
  rw [← Finset.mul_sum, M.P_sum_one, mul_one]

theorem solution {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ) (n₁ n₂ n₃ n₂' n₃' : Setting) (α : ℤˣ) :
    ∑ β, ∑ γ, M.predict n₁ n₂ n₃ α β γ = ∑ β, ∑ γ, M.predict n₁ n₂' n₃' α β γ := by
  rw [marginal_formula, marginal_formula]
