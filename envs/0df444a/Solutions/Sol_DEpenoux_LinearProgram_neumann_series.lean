-- Prove2me | solution 1 for DEpenoux.LinearProgram.neumann_series
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:34:05.013994+00:00
-- url     : https://prove2.me/submissions/af276a27-37ea-4c00-9514-a1cb3cead34a

import Mathlib

set_option autoImplicit false

theorem solution {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (hP0 : ∀ i k, 0 ≤ P i k) (hP1 : ∀ i, ∑ k, P i k = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    IsUnit (1 - lam • P) ∧
      HasSum (fun k : ℕ => lam ^ k • P ^ k) (1 - lam • P)⁻¹ := by
  let _ : NormedRing (Matrix (Fin m) (Fin m) ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) := Matrix.linftyOpNormedSpace
  have hPn : ‖P‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => le_of_eq ?_
    apply NNReal.eq
    push_cast
    rw [← hP1 i]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Real.norm_of_nonneg (hP0 i k)
  have hPn' : ‖P‖ ≤ 1 := by exact_mod_cast hPn
  have hx : ‖lam • P‖ < 1 := by
    calc ‖lam • P‖ ≤ ‖lam‖ * ‖P‖ := norm_smul_le _ _
      _ ≤ lam * 1 := by
          rw [Real.norm_eq_abs, abs_of_pos hlam0]
          exact mul_le_mul_of_nonneg_left hPn' hlam0.le
      _ < 1 := by linarith
  refine ⟨(Units.oneSub (lam • P) hx).isUnit, ?_⟩
  have hs := (summable_geometric_of_norm_lt_one hx).hasSum
  have hinv : (1 - lam • P)⁻¹ = ∑' i : ℕ, (lam • P) ^ i :=
    Matrix.inv_eq_right_inv (mul_neg_geom_series _ hx)
  rw [hinv]
  simp only [smul_pow] at hs ⊢
  exact hs
