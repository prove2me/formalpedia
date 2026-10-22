-- Prove2me | solution 1 for FRBSplitting.ThreeOp.energy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:19:05.820824+00:00
-- url     : https://prove2.me/submissions/0a56c23a-a99e-4428-8dee-eef329a2e636

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_ThreeOp_Setting
set_option autoImplicit false
open InnerProductSpace ThreeOpSplitting.Accel

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (L₁ L₂ lam : ℝ)
    (hL₁ : 0 ≤ L₁) (hBL : IsLipschitzOp L₁ B)
    (hL₂ : 0 < L₂)
    (hlam0 : 0 < lam) (hlam1 : lam < 2 / (4 * L₁ + L₂))
    (x : ℕ → H) (xs : H) :
    ∀ k : ℕ, 0 ≤ ‖x (k + 2) - xs‖ ^ 2 + 2 * lam * ⟪B (x (k + 2)) - B (x (k + 1)), xs - x (k + 2)⟫_ℝ
        + lam * L₁ * ‖x (k + 2) - x (k + 1)‖ ^ 2 := by
  intro k
  have hpos : 0 < 4 * L₁ + L₂ := by linarith
  have h1 : lam * (4 * L₁ + L₂) < 2 := by
    have := (lt_div_iff₀ hpos).mp hlam1
    exact this
  have ht1 : lam * L₁ ≤ 1 := by nlinarith
  have ht0 : 0 ≤ lam * L₁ := mul_nonneg hlam0.le hL₁
  set u := x (k + 2) - xs with hu
  set d := x (k + 2) - x (k + 1) with hd
  set ΔB := B (x (k + 2)) - B (x (k + 1)) with hΔ
  have hneg : ⟪ΔB, xs - x (k + 2)⟫_ℝ = -⟪ΔB, u⟫_ℝ := by
    rw [hu, ← inner_neg_right]; congr 1; abel
  have hcs : ⟪ΔB, u⟫_ℝ ≤ ‖ΔB‖ * ‖u‖ := real_inner_le_norm _ _
  have hlip : ‖ΔB‖ ≤ L₁ * ‖d‖ := hBL _ _
  have hnu := norm_nonneg u
  have hnd := norm_nonneg d
  have hnB := norm_nonneg ΔB
  rw [hneg]
  have h2 : ‖ΔB‖ * ‖u‖ ≤ L₁ * ‖d‖ * ‖u‖ := mul_le_mul_of_nonneg_right hlip hnu
  have h3 : lam * (L₁ * ‖d‖ * ‖u‖) ≥ lam * ⟪ΔB, u⟫_ℝ := by
    apply mul_le_mul_of_nonneg_left _ hlam0.le; linarith
  have h4 : (lam * L₁) ^ 2 ≤ lam * L₁ := by nlinarith
  have h5 : 0 ≤ (‖u‖ - lam * L₁ * ‖d‖) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖d‖)]
