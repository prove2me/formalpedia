-- Prove2me | solution 1 for DerivativeChainContinuation.first_derivative_unique_nearest
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:42:06.598245+00:00
-- url     : https://prove2.me/submissions/5c28ebf4-339c-4093-b089-d6c804142370

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_last_derivative_unique_nearest
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators









theorem realRootProduct_reflect {n : ℕ} (a : Fin n → ℝ) :
    realRootProduct (fun i => -a i.rev) =
      C ((-1 : ℝ)^n)*(realRootProduct a).comp (-X) := by
  have hfactor (i : Fin n) :
      X-C (-a i) = C (-1 : ℝ)*(X-C (a i)).comp (-X) := by
    simp only [sub_comp,X_comp,C_comp]
    simp only [map_neg,map_one]
    ring
  have hperm : realRootProduct (fun i => -a i.rev) = realRootProduct (fun i => -a i) := by
    unfold realRootProduct
    exact Equiv.prod_comp Fin.revPerm (fun i => X-C (-a i))
  rw [hperm]
  simp only [realRootProduct,hfactor,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,←map_pow,Polynomial.prod_comp]

theorem reflect_derivative (n : ℕ) (a : Fin (n+3) → ℝ)
    (b : Fin (n+2) → ℝ)
    (hder : (realRootProduct a).derivative = C (n+3 : ℝ)*realRootProduct b) :
    (realRootProduct (fun i => -a i.rev)).derivative =
      C (n+3 : ℝ)*realRootProduct (fun i => -b i.rev) := by
  rw [realRootProduct_reflect,derivative_mul,derivative_C,zero_mul,zero_add,
    derivative_comp,hder,mul_comp,C_comp,derivative_neg,derivative_X,
    realRootProduct_reflect]
  simp only [map_pow,map_neg,map_one]
  rw [show n+3=(n+2)+1 by omega,pow_succ]
  ring



















end DerivativeChainContinuation

theorem solution (n : ℕ) (a : Fin (n+3) → ℝ)
    (b : Fin (n+2) → ℝ) (ha : Monotone a) (hb : Monotone b)
    (hinter : ∀ i : Fin (n+2), a i.castSucc ≤ b i ∧ b i ≤ a i.succ)
    (hder : (realRootProduct a).derivative = C (n+3 : ℝ)*realRootProduct b)
    (i : Fin (n+3)) (hi : a i ≠ a 0) :
    |a 0-b 0| < |a i-b 0| := by
  have hmA : Monotone (fun i : Fin (n+3) => -a i.rev) := by
    intro i j hij
    exact neg_le_neg (ha (Fin.rev_le_rev.mpr hij))
  have hmB : Monotone (fun i : Fin (n+2) => -b i.rev) := by
    intro i j hij
    exact neg_le_neg (hb (Fin.rev_le_rev.mpr hij))
  have hI : ∀ i : Fin (n+2),
      -a i.castSucc.rev ≤ -b i.rev ∧ -b i.rev ≤ -a i.succ.rev := by
    intro i
    have h := hinter i.rev
    constructor
    · simpa only [Fin.rev_castSucc] using neg_le_neg h.2
    · simpa only [Fin.rev_succ] using neg_le_neg h.1
  have h := last_derivative_unique_nearest n _ _ hmA hmB hI
    (reflect_derivative n a b hder) i.rev (by simpa using hi)
  simpa only [Fin.rev_rev,Fin.rev_last,neg_sub_neg,abs_sub_comm] using h
