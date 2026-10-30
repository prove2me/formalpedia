-- Prove2me | solution 1 for DerivativeChainContinuation.positive_weighted_outer_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:32:41.664996+00:00
-- url     : https://prove2.me/submissions/be37533e-9452-4e6a-aa82-64ae977c5761

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_weighted_last_midpoint
import Theorems.Thm_DerivativeChainContinuation_real_derivative_interlacing
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







theorem realRootProduct_eval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    (realRootProduct a).eval (a i) = 0 := by
  simp only [realRootProduct, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)




end DerivativeChainContinuation

theorem solution (d s k : ℕ) (a : Fin (d+2) → ℝ)
    (ha : Monotone a) (hpositive : ∀ i,0<a i) (hk : 1 ≤ k)
    (t : ℝ) (ht : 0<t) (hroot : (positiveWeighted s k (realRootProduct a)).eval t=0)
    (hmax : ∀ x : ℝ,0<x → (positiveWeighted s k (realRootProduct a)).eval x=0 → x ≤ t) :
    (a (Fin.last d).castSucc+a (Fin.last (d+1)))/2 ≤ t := by
  by_cases hgap : a (Fin.last d).castSucc<a (Fin.last (d+1))
  · exact positive_weighted_last_midpoint d s k a ha hpositive hk hgap t ht hroot hmax
  · have heq : a (Fin.last d).castSucc=a (Fin.last (d+1)) :=
      le_antisymm (ha (Fin.le_last _)) (le_of_not_gt hgap)
    obtain ⟨b,hb,hinter,hder⟩ := real_derivative_interlacing d a ha
    have hblast : b (Fin.last d)=a (Fin.last (d+1)) := by
      have hi := hinter (Fin.last d)
      simp only [Fin.succ_last] at hi
      linarith
    have hd : (realRootProduct a).derivative.eval (a (Fin.last (d+1)))=0 := by
      rw [hder,eval_mul,eval_C,←hblast,realRootProduct_eval,mul_zero]
    have hweighted : (positiveWeighted s k (realRootProduct a)).eval
        (a (Fin.last (d+1)))=0 := by
      simp only [positiveWeighted,eval_add,eval_mul,eval_C,eval_X,
        realRootProduct_eval,hd,mul_zero,zero_add]
    have hm := hmax _ (hpositive _) hweighted
    rw [heq]
    linarith
