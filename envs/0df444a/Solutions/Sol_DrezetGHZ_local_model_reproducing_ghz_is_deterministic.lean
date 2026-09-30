-- Prove2me | solution 1 for DrezetGHZ.local_model_reproducing_ghz_is_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:30:19.658825+00:00
-- url     : https://prove2.me/submissions/ab9aef79-787d-4475-9f5c-73d64c805826

import Definitions.Def_DrezetGHZ_Models
set_option autoImplicit false
open DrezetGHZ MeasureTheory Matrix

set_option maxHeartbeats 800000 in
private theorem born_cases (α β γ : ℤˣ) :
    bornProb .x .x .x α β γ = (if α * β * γ = -1 then 1 / 4 else 0) ∧
    bornProb .x .y .y α β γ = (if α * β * γ = 1 then 1 / 4 else 0) ∧
    bornProb .y .x .y α β γ = (if α * β * γ = 1 then 1 / 4 else 0) ∧
    bornProb .y .y .x α β γ = (if α * β * γ = 1 then 1 / 4 else 0) := by
  have hs2r : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast hs2r
  have hs4 : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
    calc
      (Real.sqrt 2 : ℂ) ^ 4 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  rcases Int.units_eq_one_or α with rfl | rfl <;>
    rcases Int.units_eq_one_or β with rfl | rfl <;>
    rcases Int.units_eq_one_or γ with rfl | rfl <;>
    norm_num [bornProb, productKet, spinEigenvector, dotProduct, ghzState,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.sq_sqrt] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.normSq_mul, hs4,
      Complex.normSq_ofReal, Real.sq_sqrt]

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


private theorem wrong_product_zero {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ) (n₁ n₂ n₃ : Setting) (s : ℤˣ)
    (h : ∀ α β γ : ℤˣ, α * β * γ ≠ s → M.predict n₁ n₂ n₃ α β γ = 0) :
    ∀ᵐ lam ∂M.ρ, ∀ α β γ : ℤˣ, α * β * γ ≠ s →
      M.P 0 lam n₁ α * M.P 1 lam n₂ β * M.P 2 lam n₃ γ = 0 := by
  simp only [ae_all_iff]
  intro α β γ he
  exact (integral_eq_zero_iff_of_nonneg
    (fun lam => mul_nonneg (mul_nonneg (M.P_nonneg 0 lam n₁ α)
      (M.P_nonneg 1 lam n₂ β)) (M.P_nonneg 2 lam n₃ γ))
    (response_product_integrable M n₁ n₂ n₃ α β γ)).mp (h α β γ he)

private theorem positive_response {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ) (lam : Λ) (j : Fin 3) (n : Setting) :
    ∃ α : ℤˣ, 0 < M.P j lam n α := by
  by_contra hn
  push_neg at hn
  have hh : ∑ α, M.P j lam n α ≤ 0 := Finset.sum_nonpos (fun a _ => hn a)
  rw [M.P_sum_one] at hh
  norm_num at hh

set_option maxHeartbeats 800000 in
private theorem no_bell_local {Λ : Type*} [MeasurableSpace Λ] (M : LocalCausalModel Λ) :
    ¬ ((∀ α β γ : ℤˣ, M.predict .x .x .x α β γ = bornProb .x .x .x α β γ) ∧
       (∀ α β γ : ℤˣ, M.predict .x .y .y α β γ = bornProb .x .y .y α β γ) ∧
       (∀ α β γ : ℤˣ, M.predict .y .x .y α β γ = bornProb .y .x .y α β γ) ∧
       (∀ α β γ : ℤˣ, M.predict .y .y .x α β γ = bornProb .y .y .x α β γ)) := by
  rintro ⟨hxxx, hxyy, hyxy, hyyx⟩
  have hx := wrong_product_zero M .x .x .x (-1) (by
    intro α β γ he
    rw [hxxx, (born_cases α β γ).1, if_neg he])
  have hxy := wrong_product_zero M .x .y .y 1 (by
    intro α β γ he
    rw [hxyy, (born_cases α β γ).2.1, if_neg he])
  have hyx := wrong_product_zero M .y .x .y 1 (by
    intro α β γ he
    rw [hyxy, (born_cases α β γ).2.2.1, if_neg he])
  have hyy := wrong_product_zero M .y .y .x 1 (by
    intro α β γ he
    rw [hyyx, (born_cases α β γ).2.2.2, if_neg he])
  letI := M.isProbabilityMeasure
  obtain ⟨lam, h₁, h₂, h₃, h₄⟩ := (hx.and (hxy.and (hyx.and hyy))).exists
  obtain ⟨a₀, ha₀⟩ := positive_response M lam 0 .x
  obtain ⟨a₁, ha₁⟩ := positive_response M lam 1 .x
  obtain ⟨a₂, ha₂⟩ := positive_response M lam 2 .x
  obtain ⟨b₀, hb₀⟩ := positive_response M lam 0 .y
  obtain ⟨b₁, hb₁⟩ := positive_response M lam 1 .y
  obtain ⟨b₂, hb₂⟩ := positive_response M lam 2 .y
  have e₁ : a₀ * a₁ * a₂ = -1 := by
    by_contra hn
    have hpos := mul_pos (mul_pos ha₀ ha₁) ha₂
    rw [h₁ a₀ a₁ a₂ hn] at hpos
    exact (lt_irrefl 0 hpos)
  have e₂ : a₀ * b₁ * b₂ = 1 := by
    by_contra hn
    have hpos := mul_pos (mul_pos ha₀ hb₁) hb₂
    rw [h₂ a₀ b₁ b₂ hn] at hpos
    exact (lt_irrefl 0 hpos)
  have e₃ : b₀ * a₁ * b₂ = 1 := by
    by_contra hn
    have hpos := mul_pos (mul_pos hb₀ ha₁) hb₂
    rw [h₃ b₀ a₁ b₂ hn] at hpos
    exact (lt_irrefl 0 hpos)
  have e₄ : b₀ * b₁ * a₂ = 1 := by
    by_contra hn
    have hpos := mul_pos (mul_pos hb₀ hb₁) ha₂
    rw [h₄ b₀ b₁ a₂ hn] at hpos
    exact (lt_irrefl 0 hpos)
  have hs (u : ℤˣ) : u * u = 1 := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  have hf : a₀ * a₁ * a₂ = 1 := by
    calc
      a₀ * a₁ * a₂ = a₀ * a₁ * a₂ * (b₀ * b₀) * (b₁ * b₁) * (b₂ * b₂) := by
        rw [hs, hs, hs]; simp
      _ = (a₀ * b₁ * b₂) * (b₀ * a₁ * b₂) * (b₀ * b₁ * a₂) := by ac_rfl
      _ = 1 := by rw [e₂, e₃, e₄]; simp
  rw [e₁] at hf
  norm_num at hf

theorem solution {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ)
    (hxxx : ∀ α β γ : ℤˣ, M.predict .x .x .x α β γ = bornProb .x .x .x α β γ)
    (hxyy : ∀ α β γ : ℤˣ, M.predict .x .y .y α β γ = bornProb .x .y .y α β γ)
    (hyxy : ∀ α β γ : ℤˣ, M.predict .y .x .y α β γ = bornProb .y .x .y α β γ)
    (hyyx : ∀ α β γ : ℤˣ, M.predict .y .y .x α β γ = bornProb .y .y .x α β γ) :
    ∀ᵐ lam ∂M.ρ, ∃ A B : Fin 3 → ℤˣ,
      (∀ j α, M.P j lam .x α = if α = A j then 1 else 0) ∧
      (∀ j α, M.P j lam .y α = if α = B j then 1 else 0) ∧
      A 0 * A 1 * A 2 = -1 ∧
      A 0 * B 1 * B 2 = 1 ∧
      B 0 * A 1 * B 2 = 1 ∧
      B 0 * B 1 * A 2 = 1 := by
  exact (no_bell_local M ⟨hxxx, hxyy, hyxy, hyyx⟩).elim
