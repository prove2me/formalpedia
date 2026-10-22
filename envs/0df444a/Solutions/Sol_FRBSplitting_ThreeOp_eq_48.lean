-- Prove2me | solution 1 for FRBSplitting.ThreeOp.eq_48
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:19:37.273682+00:00
-- url     : https://prove2.me/submissions/16ef6bee-40be-4409-b156-e584b60a76bc

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_ThreeOp_Setting
set_option autoImplicit false
open InnerProductSpace ThreeOpSplitting.Accel FRBSplitting.ThreeOp

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B C : H → H) (J : ℝ → H → H) (lam : ℝ)
    (hA : IsMonotoneOp A)
    (hJ : IsResolventFamily A J)
    (hlam0 : 0 < lam)
    (x : ℕ → H) (hrun : IsThreeOpRun J B C lam x)
    (xs : H) (hxs : xs ∈ FRBSplitting.Weak.zeroSet A (fun y => B y + C y)) :
    ∀ k : ℕ, 0 ≤ ⟪x (k + 2) - x (k + 1), xs - x (k + 2)⟫_ℝ
        + lam * ⟪B (x (k + 1)) - B xs, xs - x (k + 2)⟫_ℝ
        + lam * ⟪B (x (k + 1)) - B (x k), xs - x (k + 1)⟫_ℝ
        + lam * ⟪B (x (k + 1)) - B (x k), x (k + 1) - x (k + 2)⟫_ℝ
        + lam * ⟪C (x (k + 1)) - C xs, xs - x (k + 1)⟫_ℝ
        + lam * ⟪C (x (k + 1)) - C xs, x (k + 1) - x (k + 2)⟫_ℝ := by
  intro k
  have hres := hJ lam hlam0 (x (k + 1) - (2 * lam) • B (x (k + 1)) + lam • B (x k) - lam • C (x (k + 1)))
  rw [← hrun k] at hres
  have hm := hA _ _ _ _ hres hxs
  have hl : lam ≠ 0 := hlam0.ne'
  have key : ⟪x (k + 2) - x (k + 1), xs - x (k + 2)⟫_ℝ
        + lam * ⟪B (x (k + 1)) - B xs, xs - x (k + 2)⟫_ℝ
        + lam * ⟪B (x (k + 1)) - B (x k), xs - x (k + 1)⟫_ℝ
        + lam * ⟪B (x (k + 1)) - B (x k), x (k + 1) - x (k + 2)⟫_ℝ
        + lam * ⟪C (x (k + 1)) - C xs, xs - x (k + 1)⟫_ℝ
        + lam * ⟪C (x (k + 1)) - C xs, x (k + 1) - x (k + 2)⟫_ℝ
      = lam * ⟪x (k + 2) - xs, lam⁻¹ • (x (k + 1) - (2 * lam) • B (x (k + 1)) + lam • B (x k) - lam • C (x (k + 1)) - x (k + 2)) - -(B xs + C xs)⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, inner_neg_left, inner_neg_right, real_inner_comm]
    field_simp
    ring
  rw [key]
  exact mul_nonneg hlam0.le hm
