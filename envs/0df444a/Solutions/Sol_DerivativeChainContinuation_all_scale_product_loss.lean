-- Prove2me | solution 1 for DerivativeChainContinuation.all_scale_product_loss
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:51:39.173376+00:00
-- url     : https://prove2.me/submissions/bdea2e8c-4a87-490b-8149-bd046e0f7385

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finite_product_inverse_loss
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution {ι : Type*} [Fintype ι]
    (d q : ι → ℝ) (t g : ℝ) (ht : 0 < t) (hg : 0 < g)
    (hd : ∀ i,t ≤ d i) (hq : ∀ i,0 ≤ q i)
    (hupper : g ≤ ∏ i,(d i+q i)) :
    1-(∏ i,d i)/g ≤ min 1 ((∑ i,q i)/t) := by
  classical
  let x := fun i => q i/d i
  have hd0 (i : ι) : 0 < d i := ht.trans_le (hd i)
  have hx (i : ι) : 0 ≤ x i := div_nonneg (hq i) (hd0 i).le
  have hp : 0 < ∏ i,d i := Finset.prod_pos (fun i _ => hd0 i)
  have hQ : 0 < ∏ i,(1+x i) := Finset.prod_pos (fun i _ => by linarith [hx i])
  have hfactor : (∏ i,(d i+q i))=(∏ i,d i)*(∏ i,(1+x i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [x]
    field_simp [(hd0 i).ne']
    <;> ring
  have hr : (∏ i,(1+x i))⁻¹ ≤ (∏ i,d i)/g := by
    apply (le_div_iff₀ hg).mpr
    rw [hfactor] at hupper
    have hh := mul_le_mul_of_nonneg_right hupper (inv_nonneg.mpr hQ.le)
    simpa only [mul_assoc,mul_inv_cancel₀ hQ.ne',mul_one,mul_comm] using hh
  have hs : (∑ i,x i) ≤ (∑ i,q i)/t := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    dsimp [x]
    exact div_le_div_of_nonneg_left (hq i) ht (hd i)
  have h := (finite_product_inverse_loss Finset.univ x (fun i _ => hx i)).2
  exact (sub_le_sub_left hr 1).trans (h.trans (min_le_min_left 1 hs))
