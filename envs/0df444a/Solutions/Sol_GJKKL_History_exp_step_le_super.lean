-- Prove2me | solution 1 for GJKKL.History.exp_step_le_super
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:20.617802+00:00
-- url     : https://prove2.me/submissions/f1936bfa-0937-442f-9c53-275821197e56

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_Pseudorandom_exp_le_one_add_add_sq_div
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
namespace GJKKL.History
theorem _root_.solution {β : Type*} [Fintype β] (p : β → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a ≤ 1) (Δ : β → ℝ) (hmean : ∑ a, p a * Δ a ≤ 0) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hθC : θ * C < 1) (hΔ : ∀ a, p a ≠ 0 → |Δ a| ≤ C) :
    ∑ a, p a * Real.exp (θ * Δ a) ≤
      Real.exp (θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a|) := by
  have hK : 0 < 2 * (1 - θ * C) := by linarith
  have hpt : ∀ a, p a * Real.exp (θ * Δ a) ≤
      p a * (1 + θ * Δ a + θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a|) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    apply mul_le_mul_of_nonneg_left _ (hp0 a)
    have hC := hΔ a hpa
    have h1 := Pseudorandom.exp_le_one_add_add_sq_div (θ * Δ a) (θ * C)
      (by rw [abs_mul, abs_of_nonneg hθ]; exact mul_le_mul_of_nonneg_left hC hθ) hθC
    have h2 : (θ * Δ a) ^ 2 / (2 * (1 - θ * C)) ≤ θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a| := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hK.le
      have : Δ a ^ 2 ≤ C * |Δ a| := by
        rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_right hC (abs_nonneg _)
      calc (θ * Δ a) ^ 2 = θ ^ 2 * Δ a ^ 2 := by ring
        _ ≤ θ ^ 2 * (C * |Δ a|) := mul_le_mul_of_nonneg_left this (sq_nonneg θ)
        _ = θ ^ 2 * C * |Δ a| := by ring
    linarith
  calc ∑ a, p a * Real.exp (θ * Δ a)
      ≤ ∑ a, p a * (1 + θ * Δ a + θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a|) :=
        sum_le_sum fun a _ => hpt a
    _ = ∑ a, p a + θ * ∑ a, p a * Δ a +
          θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a| := by
        rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun a _ => by ring
    _ ≤ 1 + θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a| := by
        have : θ * ∑ a, p a * Δ a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hmean
        linarith
    _ ≤ _ := by linarith [Real.add_one_le_exp (θ ^ 2 * C / (2 * (1 - θ * C)) *
          ∑ a, p a * |Δ a|)]
end GJKKL.History
