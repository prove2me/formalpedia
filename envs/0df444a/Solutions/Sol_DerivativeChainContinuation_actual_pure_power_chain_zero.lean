-- Prove2me | solution 1 for DerivativeChainContinuation.actual_pure_power_chain_zero
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:11:55.550511+00:00
-- url     : https://prove2.me/submissions/85355620-d296-48b2-a5f7-efb0ec71dc38

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution {n : ℕ} (a z : Fin (n+1) → ℂ)
    (hp : fromRoots a=X^(n+1)) (hz : DerivativeChainPrivate.IsChain a z) :
    (∀ i,z i=0) ∧ chainCost z=0 := by
  have hzero (i : Fin (n+1)) : z i=0 := by
    have hroot := hz i
    rw [row,hp,iterate_derivative_X_pow_eq_C_mul,eval_mul,eval_C,eval_pow,eval_X] at hroot
    have hdesc : 0<(n+1).descFactorial (n+1-(i.val+1)) :=
      Nat.descFactorial_pos.mpr (by omega)
    have hcoeff : ((n+1).descFactorial (n+1-(i.val+1)) : ℂ)≠0 := by
      exact_mod_cast (ne_of_gt hdesc)
    have he := (mul_eq_zero.mp hroot).resolve_left hcoeff
    exact (eq_zero_of_pow_eq_zero he)
  refine ⟨hzero,?_⟩
  simp only [chainCost,hzero,sub_self,norm_zero,Finset.sum_const_zero]
