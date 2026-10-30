-- Prove2me | solution 1 for DerivativeChainContinuation.centered_ordered_transport
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:41:43.857024+00:00
-- url     : https://prove2.me/submissions/16cd6231-b625-488d-a995-140c1765c831

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealHistories
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainContinuation_RealTransportBound
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_realHistoryCost_attained
import Theorems.Thm_DerivativeChainContinuation_real_tower_cost_square_bound
import Theorems.Thm_DerivativeChainContinuation_real_tower_exists
import Theorems.Thm_DerivativeChainContinuation_real_tower_factor
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
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


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators





theorem rowHistory_is_derivative_chain (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (z : Fin (n+1) → ℝ) (hz : IsRowHistory r z) :
    IsRealDerivativeChain (realRootProduct (r n)) n z := by
  intro i
  obtain ⟨c,hc,heq⟩ := real_tower_factor r n hstep i.val (by omega)
  obtain ⟨j,hj⟩ := hz i
  rw [heq,eval_mul,eval_C,hj,realRootProduct_eval,mul_zero]






end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0<n) (a : Fin (n+1) → ℝ)
    (ha : Monotone a) (hc : ∑ i,a i=0) :
    ∃ z : Fin (n+1) → Fin (n+1) → ℝ,
      (∀ j,IsRealDerivativeChain (realRootProduct a) n (z j)) ∧
      (∀ j,z j (Fin.last n)=a j) ∧
      (∑ j,(realChainCost (z j))^2) ≤ (28/3 : ℝ)*(∑ i,(a i)^2) := by
  obtain ⟨r,hr,_,hstep⟩ := real_tower_exists n a ha
  have hc' : ∑ i,r n i=0 := by rw [hr]; exact hc
  have hex (j : Fin (n+1)) := realHistoryCost_attained r n (r n j) ⟨j,rfl⟩
  choose z hz using hex
  refine ⟨z,?_,?_,?_⟩
  · intro j
    simpa only [hr] using rowHistory_is_derivative_chain r n hstep (z j) (hz j).1
  · intro j
    simpa only [hr] using (hz j).2.1
  · have h := real_tower_cost_square_bound r n hn hstep hc'
    simpa only [(fun j => (hz j).2.2),hr] using h
