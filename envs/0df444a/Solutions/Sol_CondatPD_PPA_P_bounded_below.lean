-- Prove2me | solution 1 for CondatPD.PPA.P_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:56:32.182329+00:00
-- url     : https://prove2.me/submissions/11f73aaa-0453-41d3-9889-07bac50b96c3

import Mathlib
import Definitions.Def_CondatPD_PPA_Setting

set_option autoImplicit false

namespace CondatPPAc67592f3

/-- Real core: coercivity of `a²/τ + b²/σ - 2p` when `|p| ≤ K a b` and `στK² < 1`. -/
theorem real_core (τ σ K a b p : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hK : 0 ≤ K)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : |p| ≤ K * a * b) (h : σ * τ * K ^ 2 < 1) :
    (1 - σ * τ * K ^ 2) / 2 / (τ + σ) * (a ^ 2 + b ^ 2) ≤ a ^ 2 / τ + b ^ 2 / σ - 2 * p := by
  set t := σ * τ * K ^ 2 with ht
  set m := (1 + t) / 2 with hm
  have ht0 : 0 ≤ t := by positivity
  have hm0 : 0 < m := by rw [hm]; linarith
  have hmt : t ≤ m ^ 2 := by rw [hm]; nlinarith [sq_nonneg (1 - t)]
  have key : m * σ * (m * (σ * a ^ 2 + τ * b ^ 2) - 2 * K * a * b * σ * τ)
      = (m * σ * a - K * σ * τ * b) ^ 2 + σ * τ * (m ^ 2 - t) * b ^ 2 := by
    rw [ht]; ring
  have hrhs : 0 ≤ (m * σ * a - K * σ * τ * b) ^ 2 + σ * τ * (m ^ 2 - t) * b ^ 2 := by
    have : 0 ≤ m ^ 2 - t := by linarith
    positivity
  have h1 : 2 * K * a * b * σ * τ ≤ m * (σ * a ^ 2 + τ * b ^ 2) := by
    have hmσ : 0 < m * σ := mul_pos hm0 hσ
    rw [← key] at hrhs
    have := (mul_nonneg_iff_of_pos_left hmσ).1 hrhs
    linarith
  have hpK : p ≤ K * a * b := le_trans (le_abs_self p) hp
  -- divide h1 by στ
  have hστ : 0 < σ * τ := mul_pos hσ hτ
  have h2 : 2 * (K * a * b) ≤ m * (a ^ 2 / τ + b ^ 2 / σ) := by
    have e : m * (a ^ 2 / τ + b ^ 2 / σ) = m * (σ * a ^ 2 + τ * b ^ 2) / (σ * τ) := by
      field_simp
    rw [e, le_div_iff₀ hστ]
    linarith
  have hδ : 0 ≤ (1 - t) / 2 := by linarith
  have h3 : (1 - t) / 2 / (τ + σ) * (a ^ 2 + b ^ 2) ≤ (1 - t) / 2 * (a ^ 2 / τ + b ^ 2 / σ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have e1 : a ^ 2 / τ * (τ + σ) = a ^ 2 + a ^ 2 * σ / τ := by field_simp
    have e2 : b ^ 2 / σ * (τ + σ) = b ^ 2 + b ^ 2 * τ / σ := by field_simp; ring
    have f1 : 0 ≤ a ^ 2 * σ / τ := by positivity
    have f2 : 0 ≤ b ^ 2 * τ / σ := by positivity
    have : a ^ 2 + b ^ 2 ≤ (a ^ 2 / τ + b ^ 2 / σ) * (τ + σ) := by
      rw [add_mul, e1, e2]; linarith
    calc (1 - t) / 2 * (a ^ 2 + b ^ 2) ≤ (1 - t) / 2 * ((a ^ 2 / τ + b ^ 2 / σ) * (τ + σ)) :=
          mul_le_mul_of_nonneg_left this hδ
      _ = _ := by ring
  have : (1 - t) / 2 = 1 - m := by rw [hm]; ring
  rw [this] at h3 ⊢
  nlinarith [h2, h3, hpK]

end CondatPPAc67592f3

open CondatPD.PPA InnerProductSpace in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (h_i : σ * τ * ‖L‖ ^ 2 < 1) :
    (∃ c : ℝ, 0 < c ∧ ∀ (x : X) (y : Y), c * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ qP τ σ L x y) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ (x : X) (y : Y), c * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ qP' τ σ L x y) := by
  have hc : 0 < (1 - σ * τ * ‖L‖ ^ 2) / 2 / (τ + σ) := by
    apply div_pos <;> linarith
  have hbd : ∀ (x : X) (y : Y), |⟪L x, y⟫_ℝ| ≤ ‖L‖ * ‖x‖ * ‖y‖ := fun x y =>
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm x) (norm_nonneg _))
  have hx : ∀ x : X, ⟪x, τ⁻¹ • x⟫_ℝ = ‖x‖ ^ 2 / τ := fun x => by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have hy : ∀ y : Y, ⟪y, σ⁻¹ • y⟫_ℝ = ‖y‖ ^ 2 / σ := fun y => by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have hadj : ∀ (x : X) (y : Y), ⟪x, ContinuousLinearMap.adjoint L y⟫_ℝ = ⟪L x, y⟫_ℝ :=
    fun x y => by rw [ContinuousLinearMap.adjoint_inner_right]
  have hyL : ∀ (x : X) (y : Y), ⟪y, L x⟫_ℝ = ⟪L x, y⟫_ℝ := fun x y => real_inner_comm _ _
  refine ⟨⟨_, hc, fun x y => ?_⟩, ⟨_, hc, fun x y => ?_⟩⟩
  · have e : qP τ σ L x y = ‖x‖ ^ 2 / τ + ‖y‖ ^ 2 / σ - 2 * ⟪L x, y⟫_ℝ := by
      simp only [qP, inner_sub_right, inner_add_right, inner_neg_right, hx, hy, hadj, hyL]
      ring
    rw [e]
    exact CondatPPAc67592f3.real_core τ σ ‖L‖ ‖x‖ ‖y‖ _ hτ hσ (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (hbd x y) h_i
  · have e : qP' τ σ L x y = ‖x‖ ^ 2 / τ + ‖y‖ ^ 2 / σ - 2 * (-⟪L x, y⟫_ℝ) := by
      simp only [qP', inner_add_right, hx, hy, hadj, hyL]
      ring
    rw [e]
    exact CondatPPAc67592f3.real_core τ σ ‖L‖ ‖x‖ ‖y‖ _ hτ hσ (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (by rw [abs_neg]; exact hbd x y) h_i
