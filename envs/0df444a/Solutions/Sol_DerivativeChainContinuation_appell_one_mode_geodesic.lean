-- Prove2me | solution 1 for DerivativeChainContinuation.appell_one_mode_geodesic
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:48:13.065746+00:00
-- url     : https://prove2.me/submissions/fab455bd-5018-4d12-8628-a0403c106b76

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_BinomialRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_appellRow_one_mode
import Theorems.Thm_DerivativeChainContinuation_binomial_geodesic_to_root
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem appellRow_coeff (m k : ℕ) (c : ℕ → ℂ) :
    (appellRow m c).coeff k = if k ≤ m then (m.choose k:ℂ)*c (m-k) else 0 := by
  classical
  simp only [appellRow,finsetSum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  simp [Finset.sum_ite_eq',Nat.lt_succ_iff]

theorem appellRow_coeff_eq (m k : ℕ) (c : ℕ → ℂ) :
    (appellRow m c).coeff k = (m.choose k:ℂ)*c (m-k) := by
  rw [appellRow_coeff]
  split_ifs with hk
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]







theorem appellRow_derivative (m : ℕ) (c : ℕ → ℂ) :
    (appellRow (m+1) c).derivative = C (m+1:ℂ)*appellRow m c := by
  ext k
  rw [coeff_derivative,coeff_C_mul,appellRow_coeff_eq,appellRow_coeff_eq]
  have hch : (m+1:ℂ)*(m.choose k:ℂ) = ((m+1).choose (k+1):ℂ)*(k+1:ℂ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq m k
  rw [show m+1-(k+1)=m-k by omega]
  push_cast
  linear_combination -c (m-k)*hch

theorem appellRow_iterate_derivative (m k : ℕ) (c : ℕ → ℂ) :
    derivative^[k] (appellRow (m+k) c) = C ((m+k).descFactorial k:ℂ)*appellRow m c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m+Nat.succ k=(m+k)+1 by omega,Function.iterate_succ_apply,
      appellRow_derivative,iterate_derivative_C_mul,ih,← mul_assoc,← C_mul]
    rw [Nat.succ_descFactorial_succ]
    push_cast
    rfl

end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial





end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (M q : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (c : ℕ → ℂ) (hc0 : c 0=1)
    (hs : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (b : ℂ) (hb : b^q= -((M.choose q:ℂ)*c q)) :
    ∃ z : ℕ → ℂ, z 0=0 ∧ z (M-1)=b ∧
      (∀ i < M, (appellRow (i+1) c).eval (z i)=0) ∧
      (∀ i < M-1, ‖z (i+1)-z i‖ = ‖z (i+1)‖-‖z i‖) := by
  obtain ⟨z,hz0,hzend,hzroot,hzstep⟩ := binomial_geodesic_to_root q (M-q) hq _ b hb
  have hM : q+(M-q)=M := by omega
  rw [hM] at hzend hzroot hzstep
  refine ⟨z,hz0,hzend,?_,hzstep⟩
  intro i hi
  have h := hzroot i hi
  rw [← appellRow_one_mode M q (by omega) hqM c hc0 hs] at h
  have he : i+1+(M-(i+1))=M := by omega
  have hd := appellRow_iterate_derivative (i+1) (M-(i+1)) c
  rw [he] at hd
  rw [hd,eval_mul,eval_C] at h
  apply (mul_eq_zero.mp h).resolve_left
  exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : M-(i+1) ≤ M)).ne'
