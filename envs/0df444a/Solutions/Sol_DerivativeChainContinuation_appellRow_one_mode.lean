-- Prove2me | solution 1 for DerivativeChainContinuation.appellRow_one_mode
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:43:35.745044+00:00
-- url     : https://prove2.me/submissions/c1d70799-9dd5-4ad6-9ab4-2163a40a5664

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_BinomialRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
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











end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial





end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (M q : ℕ) (hq : 0 < q) (hqM : q ≤ M)
    (c : ℕ → ℂ) (hc0 : c 0=1)
    (hs : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0) :
    appellRow M c = binomialPoly q (M-q) ((M.choose q:ℂ)*c q) := by
  ext k
  rw [appellRow_coeff_eq]
  simp only [binomialPoly,show q+(M-q)=M by omega,coeff_add,coeff_X_pow,coeff_C_mul]
  by_cases hkm : k=M
  · subst k
    simp [hc0,show M-q ≠ M by omega,show M ≠ M-q by omega]
  by_cases hkq : k=M-q
  · subst k
    rw [show M-(M-q)=q by omega,Nat.choose_symm hqM]
    simp [show M ≠ M-q by omega,show M-q ≠ M by omega]
  by_cases hkle : k ≤ M
  · have hj0 : M-k ≠ 0 := by omega
    have hjq : M-k ≠ q := by omega
    rw [hs (M-k) (by omega) hj0 hjq]
    simp [hkm,hkq,Ne.symm hkm,Ne.symm hkq]
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]
    simp [hkm,hkq,Ne.symm hkm,Ne.symm hkq]
