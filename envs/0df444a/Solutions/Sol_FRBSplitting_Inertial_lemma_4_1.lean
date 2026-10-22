-- Prove2me | solution 1 for FRBSplitting.Inertial.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:43:05.657611+00:00
-- url     : https://prove2.me/submissions/fd8af779-d255-4ee2-995a-625d07a69339

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Inertial_Setting

set_option autoImplicit false
open InnerProductSpace ThreeOpSplitting.Accel
open FRBSplitting.Inertial

lemma yfri_norm_expand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) (ρ : ℝ) :
    ‖u - ρ • v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ρ * inner ℝ u v + ρ ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma yfri_cocoer {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (L : ℝ) (hL : 0 < L) (hB : IsCocoercive L⁻¹ B) (x y : H) :
    ‖B x - B y‖ ^ 2 ≤ L * inner ℝ (B x - B y) (x - y) := by
  have := hB x y
  have h2 : L⁻¹ * ‖B x - B y‖ ^ 2 ≤ inner ℝ (B x - B y) (x - y) := this
  have := mul_le_mul_of_nonneg_left h2 hL.le
  rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] at this
  exact this

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (ρ L : ℝ) (hρ : 0 ≤ ρ) :
    (IsLipschitzOp L B → IsLipschitzOp (L + ρ) (shiftOp B ρ)) ∧
    (0 < L → IsCocoercive L⁻¹ B → ρ ≤ L / 2 → IsLipschitzOp (L - ρ) (shiftOp B ρ)) ∧
    (0 < L → IsCocoercive L⁻¹ B → L / 2 < ρ → IsLipschitzOp ρ (shiftOp B ρ)) := by
  have hdiff : ∀ x y : H, shiftOp B ρ x - shiftOp B ρ y = (B x - B y) - ρ • (x - y) := by
    intro x y
    unfold shiftOp
    simp only [smul_sub]
    abel
  refine ⟨?_, ?_, ?_⟩
  · intro hLip x y
    rw [hdiff]
    calc ‖(B x - B y) - ρ • (x - y)‖ ≤ ‖B x - B y‖ + ‖ρ • (x - y)‖ := norm_sub_le _ _
      _ ≤ L * ‖x - y‖ + ρ * ‖x - y‖ := by
          rw [norm_smul, Real.norm_of_nonneg hρ]
          exact add_le_add (hLip x y) le_rfl
      _ = (L + ρ) * ‖x - y‖ := by ring
  · intro hL hB hρL x y
    rw [hdiff]
    set u := B x - B y with hu
    set v := x - y with hv
    have hc : ‖u‖ ^ 2 ≤ L * inner ℝ u v := yfri_cocoer B L hL hB x y
    have hnu : ‖u‖ ≤ L * ‖v‖ := by
      have hcs : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
      have h1 : ‖u‖ ^ 2 ≤ L * (‖u‖ * ‖v‖) := hc.trans (mul_le_mul_of_nonneg_left hcs hL.le)
      rcases (norm_nonneg u).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · nlinarith
    have hip : inner ℝ u v ≤ L * ‖v‖ ^ 2 := by
      have hcs : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
      calc inner ℝ u v ≤ ‖u‖ * ‖v‖ := hcs
        _ ≤ (L * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hnu (norm_nonneg v)
        _ = L * ‖v‖ ^ 2 := by ring
    have hsq : ‖u - ρ • v‖ ^ 2 ≤ ((L - ρ) * ‖v‖) ^ 2 := by
      rw [yfri_norm_expand]
      have h2 : (L - 2 * ρ) * inner ℝ u v ≤ (L - 2 * ρ) * (L * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hip (by linarith)
      nlinarith [hc]
    exact abs_le_of_sq_le_sq' hsq (by nlinarith [norm_nonneg v]) |>.2
  · intro hL hB hρL x y
    rw [hdiff]
    set u := B x - B y with hu
    set v := x - y with hv
    have hc : ‖u‖ ^ 2 ≤ L * inner ℝ u v := yfri_cocoer B L hL hB x y
    have hip0 : 0 ≤ inner ℝ u v := by
      have : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
      nlinarith
    have hsq : ‖u - ρ • v‖ ^ 2 ≤ (ρ * ‖v‖) ^ 2 := by
      rw [yfri_norm_expand]
      nlinarith [mul_nonneg hip0 (by linarith : (0:ℝ) ≤ 2 * ρ - L)]
    exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2
