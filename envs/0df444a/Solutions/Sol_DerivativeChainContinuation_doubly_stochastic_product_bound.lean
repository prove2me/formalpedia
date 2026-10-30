-- Prove2me | solution 1 for DerivativeChainContinuation.doubly_stochastic_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:00:23.652684+00:00
-- url     : https://prove2.me/submissions/3601f16d-5a70-4f6b-9ffb-1089bf33901c

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

theorem stochastic_positive_mean {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1)
    (hv : ∀ i, 0 < v i) : 0 < ∑ i, w i*v i := by
  classical
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have hz := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
    linarith
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (hv j).le)
    ⟨i,Finset.mem_univ i,mul_pos hi (hv i)⟩


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (v : ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j=1)
    (hcol : ∀ j, ∑ i, w i j=1) (hv : ∀ j, 0 < v j) :
    (∏ j, v j) ≤ ∏ i, (∑ j, w i j*v j) := by
  have hm (i : ι) : 0 < ∑ j, w i j*v j := stochastic_positive_mean (w i) v (hw i) (hrow i) hv
  have hj (i : ι) : (∑ j, w i j*Real.log (v j)) ≤ Real.log (∑ j, w i j*v j) := by
    simpa only [smul_eq_mul] using strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := Finset.univ) (w := w i) (p := v) (fun j _ => hw i j) (hrow i) (fun j _ => hv j)
  have hs : (∑ j, Real.log (v j)) ≤ ∑ i, Real.log (∑ j, w i j*v j) := by
    calc
      _ = ∑ i, ∑ j, w i j*Real.log (v j) := by
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul,hcol,one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hj i
  apply (Real.log_le_log_iff (Finset.prod_pos (fun j _ => hv j))
    (Finset.prod_pos (fun i _ => hm i))).mp
  rw [Real.log_prod (fun j _ => (hv j).ne'),Real.log_prod (fun i _ => (hm i).ne')]
  exact hs
