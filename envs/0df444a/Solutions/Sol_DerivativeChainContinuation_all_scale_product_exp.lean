-- Prove2me | solution 1 for DerivativeChainContinuation.all_scale_product_exp
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:47:29.121699+00:00
-- url     : https://prove2.me/submissions/2aa5b988-1ed5-4cd1-8cf5-e2ecbe9bb034

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



theorem finite_product_exp_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∏ i ∈ s, (1+x i)) ≤ Real.exp (∑ i ∈ s, x i) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi; linarith [hx i hi]
  · intro i _; simpa [add_comm] using Real.add_one_le_exp (x i)
end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {ι : Type*} [Fintype ι]
    (d q : ι → ℝ) (t g : ℝ) (ht : 0 < t)
    (hd : ∀ i,t ≤ d i) (hq : ∀ i,0 ≤ q i)
    (hupper : g ≤ ∏ i,(d i+q i)) :
    g ≤ (∏ i,d i)*Real.exp ((∑ i,q i)/t) := by
  classical
  let x := fun i => q i/d i
  have hd0 (i : ι) : 0 < d i := ht.trans_le (hd i)
  have hx (i : ι) : 0 ≤ x i := div_nonneg (hq i) (hd0 i).le
  have hfactor : (∏ i,(d i+q i))=(∏ i,d i)*(∏ i,(1+x i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [x]
    field_simp [(hd0 i).ne']
    <;> ring
  have hs : (∑ i,x i) ≤ (∑ i,q i)/t := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (hq i) ht (hd i)
  rw [hfactor] at hupper
  exact hupper.trans (mul_le_mul_of_nonneg_left
    ((finite_product_exp_bound Finset.univ x (fun i _ => hx i)).trans (Real.exp_le_exp.mpr hs))
    (Finset.prod_nonneg (fun i _ => (hd0 i).le)))
