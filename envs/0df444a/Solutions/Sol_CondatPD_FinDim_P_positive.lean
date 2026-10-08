-- Prove2me | solution 1 for CondatPD.FinDim.P_positive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:58:04.978421+00:00
-- url     : https://prove2.me/submissions/9ce8a021-67ab-41be-9bfe-44bd2d2a2202

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

set_option autoImplicit false

open InnerProductSpace

lemma e0eb8c36_key (u v l τ σ c : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hl : 0 ≤ l)
    (hτ : 0 < τ) (hσ : 0 < σ) (hi : σ * τ * l ^ 2 ≤ 1) (hc : |c| ≤ l * u * v) :
    0 ≤ τ⁻¹ * u ^ 2 - 2 * c + σ⁻¹ * v ^ 2 ∧ 0 ≤ τ⁻¹ * u ^ 2 + 2 * c + σ⁻¹ * v ^ 2 := by
  have hst : 0 < σ * τ := mul_pos hσ hτ
  have key : 2 * (σ * τ) * (l * u * v) ≤ σ * u ^ 2 + τ * v ^ 2 := by
    have h1 : 0 ≤ (σ * u - σ * τ * l * v) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ σ * τ * v ^ 2 * (1 - σ * τ * l ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    have : σ * (σ * u ^ 2 + τ * v ^ 2 - 2 * (σ * τ) * (l * u * v))
        = (σ * u - σ * τ * l * v) ^ 2 + σ * τ * v ^ 2 * (1 - σ * τ * l ^ 2) := by ring
    have h3 : 0 ≤ σ * (σ * u ^ 2 + τ * v ^ 2 - 2 * (σ * τ) * (l * u * v)) := by
      rw [this]; linarith
    have := nonneg_of_mul_nonneg_right (by linarith [h3] : 0 ≤ σ * (σ * u ^ 2 + τ * v ^ 2 - 2 * (σ * τ) * (l * u * v))) hσ
    linarith
  have e : τ⁻¹ * u ^ 2 + σ⁻¹ * v ^ 2 = (σ * u ^ 2 + τ * v ^ 2) / (σ * τ) := by
    field_simp
  have hb : 2 * (l * u * v) ≤ τ⁻¹ * u ^ 2 + σ⁻¹ * v ^ 2 := by
    rw [e, le_div_iff₀ hst]; linarith
  have := abs_le.mp hc
  constructor <;> linarith [this.1, this.2]

open CondatPD.FinDim in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hi : σ * τ * ‖L‖ ^ 2 ≤ 1) :
    ∀ (x : X) (y : Y), 0 ≤ qP τ σ L x y ∧ 0 ≤ qP' τ σ L x y := by
  intro x y
  have hc : |⟪L x, y⟫_ℝ| ≤ ‖L‖ * ‖x‖ * ‖y‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm x) (norm_nonneg _))
  have hk := e0eb8c36_key ‖x‖ ‖y‖ ‖L‖ τ σ ⟪L x, y⟫_ℝ (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hτ hσ hi hc
  have hadj : ⟪x, ContinuousLinearMap.adjoint L y⟫_ℝ = ⟪L x, y⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hsym : ⟪y, L x⟫_ℝ = ⟪L x, y⟫_ℝ := real_inner_comm _ _
  have hxx : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have hyy : ⟪y, y⟫_ℝ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  unfold qP qP'
  simp only [inner_sub_right, inner_add_right, inner_neg_right, real_inner_smul_right]
  rw [hadj, hsym, hxx, hyy]
  constructor <;> linarith [hk.1, hk.2]
