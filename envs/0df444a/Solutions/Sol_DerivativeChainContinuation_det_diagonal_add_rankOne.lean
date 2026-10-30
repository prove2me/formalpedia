-- Prove2me | solution 1 for DerivativeChainContinuation.det_diagonal_add_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:13:55.702724+00:00
-- url     : https://prove2.me/submissions/a986352b-fe3e-4a0a-8f8a-b4432bd69283

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


theorem solution {n : ℕ} (d u v : Fin n → ℂ)
    (hd : ∀ i, d i ≠ 0) :
    (diagonal d + vecMulVec u v).det = (∏ i, d i)*(1+∑ i, v i*u i/d i) := by
  have hd' : IsUnit (diagonal d).det := by
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hr : vecMulVec u v = replicateCol Unit u * replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply]
  have hi : Ring.inverse d = fun i => (d i)⁻¹ := by
    have hu : IsUnit d := ⟨⟨d, (fun i => (d i)⁻¹),
      by funext i; exact mul_inv_cancel₀ (hd i),
      by funext i; exact inv_mul_cancel₀ (hd i)⟩, rfl⟩
    have he := Ring.inverse_mul_cancel d hu
    funext i
    have hei := congrFun he i
    change Ring.inverse d i * d i = 1 at hei
    simpa only [one_div] using (eq_div_iff (hd i)).mpr hei
  rw [hr, det_add_replicateCol_mul_replicateRow hd', det_diagonal, det_unique,
    inv_diagonal]
  simp [Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply,
    Matrix.diagonal_apply, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
    Ring.inverse_eq_inv, hi]
