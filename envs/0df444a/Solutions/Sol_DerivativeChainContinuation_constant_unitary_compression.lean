-- Prove2me | solution 1 for DerivativeChainContinuation.constant_unitary_compression
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:46:40.676482+00:00
-- url     : https://prove2.me/submissions/ee0e9781-5058-4620-83c3-95e4ada9be3d

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators
open Matrix







theorem centeringProjection_selfAdjoint (n : ℕ) :
    (centeringProjection n).conjTranspose = centeringProjection n := by
  ext i j
  simp [centeringProjection, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.of_apply, eq_comm]









end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

theorem constant_unitary_column_sum (n : ℕ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) (j : Fin n) :
    ∑ i, Q i j.succ=0 := by
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => M 0 j.succ)
    (mem_unitaryGroup_iff'.mp hQ)
  have hc : ((Real.sqrt (n+1:ℝ))⁻¹:ℂ) ≠ 0 := by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity))))
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hfirst, ← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left hc

theorem constant_unitary_projection (n : ℕ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) :
    centeringProjection (n+1)*Q = Q*diagonal (Fin.cases 0 (fun _ => 1)) := by
  have hn : (n+1:ℂ) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
  ext i j
  rw [centeringProjection, sub_mul, one_mul]
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.of_apply,
    ← Finset.mul_sum]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [hfirst, Finset.sum_const, hn, Matrix.diagonal_apply, ← mul_assoc]
  · simp [constant_unitary_column_sum n Q hQ hfirst j, Matrix.diagonal_apply]


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) :
    Q.conjTranspose*rootCompression a*Q =
      diagonal (Fin.cases 0 (fun _ => 1)) * (Q.conjTranspose*diagonal a*Q) *
        diagonal (Fin.cases 0 (fun _ => 1)) := by
  have hp := constant_unitary_projection n Q hQ hfirst
  have hps := congrArg Matrix.conjTranspose hp
  simp only [conjTranspose_mul, centeringProjection_selfAdjoint, diagonal_conjTranspose] at hps
  have hd : diagonal (star (Fin.cases (0:ℂ) (fun _ : Fin n => 1))) =
      diagonal (Fin.cases 0 (fun _ => 1)) := by
    congr 1
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp
  rw [hd] at hps
  calc
    _ = (Q.conjTranspose*centeringProjection (n+1))*diagonal a*(centeringProjection (n+1)*Q) := by
      simp only [rootCompression, Matrix.mul_assoc]
    _ = _ := by rw [hp,hps]; simp only [Matrix.mul_assoc]
