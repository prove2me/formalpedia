-- Prove2me | solution 1 for DerivativeChainContinuation.constant_unitary_tail_marginal
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:44:51.241277+00:00
-- url     : https://prove2.me/submissions/8abe5e22-deb2-4cb3-8646-516ef454ffb9

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators



theorem unitary_row_normSq_sum {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j, Complex.normSq (Q i j)=1 := by
  apply Complex.ofReal_injective
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i)
    (mem_unitaryGroup_iff.mp hQ)
  simpa only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,Complex.ofReal_one,
    Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,
    Matrix.one_apply,if_pos rfl,ite_true,mul_comm] using h




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0 < n)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) (i : Fin (n+1)) :
    (∑ j : Fin n, (n:ℝ)⁻¹*Complex.normSq (Q i j.succ))=(n+1:ℝ)⁻¹ := by
  have hc : Complex.normSq (Q i 0)=(n+1:ℝ)⁻¹ := by
    rw [hfirst, Complex.normSq_eq_norm_sq]
    simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow]
    rw [Real.sq_sqrt (by positivity)]
  have hsum := unitary_row_normSq_sum Q hQ i
  rw [Fin.sum_univ_succ,hc] at hsum
  rw [← Finset.mul_sum]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn1 : (n+1:ℝ) ≠ 0 := by positivity
  have he : (∑ j : Fin n, Complex.normSq (Q i j.succ))=1-(n+1:ℝ)⁻¹ := by linarith
  rw [he]
  field_simp
  ring
