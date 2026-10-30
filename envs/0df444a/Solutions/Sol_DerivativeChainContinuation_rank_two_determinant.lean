-- Prove2me | solution 1 for DerivativeChainContinuation.rank_two_determinant
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:56:15.424407+00:00
-- url     : https://prove2.me/submissions/9c6b0f59-2c10-45c0-b843-7416c990178b

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators





theorem inverse_diagonal_entries {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i,d i ≠ 0) :
    (diagonal d)⁻¹=diagonal (fun i => (d i)⁻¹) := by
  have hu : IsUnit d := ⟨⟨d,(fun i => (d i)⁻¹),
    by funext i; exact mul_inv_cancel₀ (hd i),
    by funext i; exact inv_mul_cancel₀ (hd i)⟩,rfl⟩
  have he := Ring.inverse_mul_cancel d hu
  have hi : Ring.inverse d=(fun i => (d i)⁻¹) := by
    funext i
    have hh := congrFun he i
    change Ring.inverse d i*d i=1 at hh
    simpa only [one_div] using (eq_div_iff (hd i)).mpr hh
  rw [inv_diagonal,hi]
end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (d u v s t : Fin n → ℂ)
    (hd : ∀ i,d i ≠ 0) :
    (diagonal d + Matrix.of (fun i j : Fin n => u i*s j+v i*t j)).det =
      (∏ i,d i)*((1+∑ i,s i*u i/d i)*(1+∑ i,t i*v i/d i)-
        (∑ i,s i*v i/d i)*(∑ i,t i*u i/d i)) := by
  let U : Matrix (Fin n) (Fin 2) ℂ := Matrix.of (fun i j => ![u i,v i] j)
  let V : Matrix (Fin 2) (Fin n) ℂ := Matrix.of (fun j i => ![s i,t i] j)
  have he : Matrix.of (fun i j : Fin n => u i*s j+v i*t j)=U*V := by
    ext i j
    simp [U,V,Matrix.mul_apply,Fin.sum_univ_two]
  have hu : IsUnit (diagonal d).det := by
    rw [det_diagonal,isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  rw [he,det_add_mul U V hu,det_diagonal,inverse_diagonal_entries d hd,det_fin_two]
  simp only [Matrix.add_apply,Matrix.one_apply,Matrix.mul_apply,Matrix.diagonal_apply,
    Matrix.of_apply,U,V,Matrix.cons_val_zero,Matrix.cons_val_one,
    ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
  norm_num
