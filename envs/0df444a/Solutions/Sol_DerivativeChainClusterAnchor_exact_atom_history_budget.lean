-- Prove2me | solution 1 for DerivativeChainClusterAnchor.exact_atom_history_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:52:58.865263+00:00
-- url     : https://prove2.me/submissions/da5185f0-47cf-4d8f-b84c-69cb87fb66ab

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterPrefix
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_ReturnPath
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_eval_zero_of_exact_cluster
import Theorems.Thm_DerivativeChainClusterAnchor_source_tower_prefix_reserve
import Theorems.Thm_DerivativeChainContinuation_closeAt_cost
import Theorems.Thm_DerivativeChainContinuation_complex_tower_factor
import Theorems.Thm_DerivativeChainContinuation_uniform_polynomial_tower
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_centroid
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial
namespace DerivativeChainClusterAnchor
noncomputable section















theorem ordinaryRow_eval_zero_iff {n m : ℕ} (a : Fin n → ℂ) (c : ℂ) :
    (ordinaryRow a m).eval c=0 ↔ (derivative^[n-m] (sourcePolynomial a)).eval c=0 := by
  have hc : ((m.factorial:ℂ)/(n.factorial:ℂ)) ≠ 0 :=
    div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m) (by exact_mod_cast Nat.factorial_ne_zero n)
  simp only [ordinaryRow,eval_mul,eval_C,mul_eq_zero,hc,false_or]



end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
noncomputable section



theorem uniform_row_centroid (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    complexCentroid (r h)=r 0 0 := by
  induction h with
  | zero => simp [complexCentroid]
  | succ h ih =>
    rw [uniform_step_centroid r h (hstep h (by omega)),ih (by omega)]













end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
namespace DerivativeChainClusterAnchor
noncomputable section



theorem complex_history_ordinary_prefix (n h : ℕ) (a : Fin (n+1) → ℂ)
    (r : ComplexRootRows) (htop : r n=a) (hstep : ∀ k<n, UniformPolynomialStep r k)
    (hh : h ≤ n) (z : Fin (h+1) → ℂ) (hz : IsComplexRowHistory r z) :
    ∀ i, (ordinaryRow a (i.val+1)).eval (z i)=0 := by
  have hp : complexRowProduct r n=sourcePolynomial a := by
    simp only [complexRowProduct,htop,sourcePolynomial]
  intro i
  obtain ⟨v,hv,hfactor⟩ := complex_tower_factor r n hstep i.val (by omega)
  obtain ⟨j,hj⟩ := hz i
  have hrow : (complexRowProduct r i.val).eval (z i)=0 := by
    simp only [complexRowProduct,eval_prod,eval_sub,eval_X,eval_C,hj]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  apply (ordinaryRow_eval_zero_iff a (z i)).mpr
  rw [show n+1-(i.val+1)=n-i.val by omega,← hp,hfactor,eval_mul,hrow,mul_zero]



end
end DerivativeChainClusterAnchor



set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators











theorem chainCost_cast_index {n m : ℕ} (h : n=m) (z : Fin m → ℂ) :
    chainCost (fun i : Fin n => z (Fin.cast h i))=chainCost z := by
  subst m
  rfl

end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
open DerivativeChainClusterAnchor


theorem solution (n t : ℕ) (a : Fin (n+1) → ℂ) (c : ℂ)
    (O : Finset (Fin (n+1))) (hcut : t+1 < n+1) (hO : O.card ≤ t+1)
    (hnear : ∀ i, i ∉ O → a i=c) :
    let u := _root_.DerivativeChainContinuation.complexCentroid a
    let V := ∑ i, (n+1:ℝ)⁻¹*‖a i-u‖^2
    ∃ z : Fin (n+1) → ℂ, _root_.DerivativeChainPrivate.IsChain a z ∧
      (∀ i, t+1 ≤ i.val → z i=c) ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ (t:ℝ)*Real.sqrt (V/(n:ℝ))+
        Real.sqrt ((t:ℝ)*V/(n:ℝ)+‖u-c‖^2) := by
  dsimp only
  obtain ⟨rows,htop,hstep⟩ := _root_.DerivativeChainContinuation.uniform_polynomial_tower n a
  have hh : t ≤ n := by omega
  obtain ⟨initial,hprefix,hbound⟩ := _root_.DerivativeChainClusterAnchor.source_tower_prefix_reserve rows n t hstep hh c
  have hordinary := _root_.DerivativeChainClusterAnchor.complex_history_ordinary_prefix n t a rows htop hstep hh initial hprefix
  let f : ℕ → ℂ := fun i => if hi : i < t+1 then initial ⟨i,hi⟩ else c
  let z : Fin (n+1) → ℂ := fun i => _root_.DerivativeChainContinuation.closeAt (t+1) f c i.val
  have hz : _root_.DerivativeChainPrivate.IsChain a z := by
    intro i
    have hrow : (_root_.DerivativeChainClusterAnchor.ordinaryRow a (i.val+1)).eval (z i)=0 := by
      by_cases hi : i.val < t+1
      · have hzi : z i=initial ⟨i.val,hi⟩ := by
          dsimp only [z,_root_.DerivativeChainContinuation.closeAt,f]
          simp only [if_pos hi,dif_pos hi]
        rw [hzi]
        exact hordinary ⟨i.val,hi⟩
      · have hc := _root_.DerivativeChainClusterAnchor.ordinaryRow_eval_zero_of_exact_cluster a c O (by omega : i.val+1 ≤ n+1)
          hO (by omega : t+1 < i.val+1) hnear
        simpa only [z,_root_.DerivativeChainContinuation.closeAt,if_neg hi] using hc
    have hr := (_root_.DerivativeChainClusterAnchor.ordinaryRow_eval_zero_iff a (z i)).mp hrow
    simpa only [_root_.DerivativeChainPrivate.row,_root_.DerivativeChainPrivate.fromRoots,_root_.DerivativeChainClusterAnchor.sourcePolynomial] using hr
  have htail : ∀ i : Fin (n+1), t+1 ≤ i.val → z i=c := by
    intro i hi
    exact if_neg (by omega : ¬i.val < t+1)
  have hsplit : (t+1)+(n-t)=n+1 := by omega
  have hcastcost : _root_.DerivativeChainPrivate.chainCost z =
      _root_.DerivativeChainPrivate.chainCost (fun i : Fin ((t+1)+(n-t)) => _root_.DerivativeChainContinuation.closeAt (t+1) f c i.val) := by
    simpa only [z,Fin.val_cast] using _root_.DerivativeChainContinuation.chainCost_cast_index hsplit.symm
      (fun i : Fin ((t+1)+(n-t)) => _root_.DerivativeChainContinuation.closeAt (t+1) f c i.val)
  have hf : (fun i : Fin (t+1) => f i.val)=initial := by
    funext i
    exact (show f i.val=initial ⟨i.val,i.isLt⟩ from dif_pos i.isLt).trans
      (congrArg initial (Fin.ext rfl))
  have hflast : f t=initial (Fin.last t) := by
    exact (show f t=initial ⟨t,Nat.lt_succ_self t⟩ from dif_pos (Nat.lt_succ_self t)).trans
      (congrArg initial (Fin.ext (by simp only [Fin.val_last])))
  have hclose := _root_.DerivativeChainContinuation.closeAt_cost (t+1) (n-t) (by omega) (by omega) f c
  have hcosteq : _root_.DerivativeChainPrivate.chainCost z=_root_.DerivativeChainPrivate.chainCost initial+‖initial (Fin.last t)-c‖ := by
    rw [hcastcost,hclose,hf,show t+1-1=t by omega,hflast,norm_sub_rev c (initial (Fin.last t))]
  have hcent : _root_.DerivativeChainContinuation.complexCentroid a=rows 0 0 := by
    simpa only [htop] using _root_.DerivativeChainPrefixLaws.uniform_row_centroid rows n hstep n le_rfl
  have hV : _root_.DerivativeChainClusterAnchor.rowCenteredVariance rows n (rows 0 0)=
      ∑ i, (n+1:ℝ)⁻¹*‖a i-_root_.DerivativeChainContinuation.complexCentroid a‖^2 := by
    simp only [_root_.DerivativeChainClusterAnchor.rowCenteredVariance,htop,hcent]
  rw [hV,← hcent] at hbound
  exact ⟨z,hz,htail,hcosteq.le.trans hbound⟩
