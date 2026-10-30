-- Prove2me | solution 1 for DerivativeChainClusterAnchor.actual_cluster_history_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:41:43.554379+00:00
-- url     : https://prove2.me/submissions/172a54a7-83f2-4223-9126-b83fd6ed3b53

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterPrefix
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Definitions.Def_DerivativeChainAnalytic_ClusterTail
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_exists_actual_root_anchor
import Theorems.Thm_DerivativeChainClusterAnchor_joint_complete_prefix_reserve
import Theorems.Thm_DerivativeChainClusterAnchor_source_cluster_tail_bound_full
import Theorems.Thm_DerivativeChainContinuation_complex_tower_factor
import Theorems.Thm_DerivativeChainContinuation_uniform_polynomial_tower
import Theorems.Thm_DerivativeChainPrefixLaws_scaled_sequence_contraction
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_centroid
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_variance_contraction
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
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

theorem sourcePolynomial_monic {n : ℕ} (a : Fin n → ℂ) : (sourcePolynomial a).Monic := by
  simpa only [sourcePolynomial] using monic_prod_X_sub_C a Finset.univ

theorem sourcePolynomial_natDegree {n : ℕ} (a : Fin n → ℂ) :
    (sourcePolynomial a).natDegree=n := by simp [sourcePolynomial]

theorem ordinaryRow_coeff_top {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) :
    (ordinaryRow a m).coeff m=1 := by
  have htop : (sourcePolynomial a).coeff n=1 := by
    simpa only [sourcePolynomial_natDegree] using (sourcePolynomial_monic a).coeff_natDegree
  have hf : (m.factorial:ℂ)*(n.descFactorial (n-m):ℂ)=(n.factorial:ℂ) := by
    have h := Nat.factorial_mul_descFactorial (Nat.sub_le n m)
    rw [Nat.sub_sub_self hm] at h
    exact_mod_cast h
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [ordinaryRow,coeff_C_mul,coeff_iterate_derivative,show m+(n-m)=n by omega,htop]
  simp only [nsmul_eq_mul,mul_one]
  rw [div_mul_eq_mul_div,hf,div_self hn]

theorem ordinaryRow_natDegree_le {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) :
    (ordinaryRow a m).natDegree ≤ m := by
  have hc : ((m.factorial:ℂ)/(n.factorial:ℂ)) ≠ 0 :=
    div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m) (by exact_mod_cast Nat.factorial_ne_zero n)
  rw [ordinaryRow,natDegree_C_mul hc]
  exact (natDegree_iterate_derivative (sourcePolynomial a) (n-m)).trans_eq
    (by rw [sourcePolynomial_natDegree,Nat.sub_sub_self hm])

theorem ordinaryRow_monic {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) :
    (ordinaryRow a m).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one m (ordinaryRow_natDegree_le a hm) (ordinaryRow_coeff_top a hm)

theorem ordinaryRow_natDegree {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) :
    (ordinaryRow a m).natDegree=m := by
  exact natDegree_eq_of_le_of_coeff_ne_zero (ordinaryRow_natDegree_le a hm)
    (by rw [ordinaryRow_coeff_top a hm]; exact one_ne_zero)



theorem ordinaryRow_eval_zero_iff {n m : ℕ} (a : Fin n → ℂ) (c : ℂ) :
    (ordinaryRow a m).eval c=0 ↔ (derivative^[n-m] (sourcePolynomial a)).eval c=0 := by
  have hc : ((m.factorial:ℂ)/(n.factorial:ℂ)) ≠ 0 :=
    div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m) (by exact_mod_cast Nat.factorial_ne_zero n)
  simp only [ordinaryRow,eval_mul,eval_C,mul_eq_zero,hc,false_or]



end
end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators





theorem complex_chainCost_snoc {n : ℕ} (z : Fin (n+1) → ℂ) (v : ℂ) :
    chainCost (Fin.snoc z v)=chainCost z+‖v-z (Fin.last n)‖ := by
  change (∑ i : Fin (n+1), ‖(Fin.snoc z v : Fin (n+2) → ℂ) i.succ-(Fin.snoc z v : Fin (n+2) → ℂ) i.castSucc‖)=
    (∑ i : Fin n, ‖z i.succ-z i.castSucc‖)+‖v-z (Fin.last n)‖
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.succ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,Fin.succ_last]






end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainClusterAnchor
noncomputable section

theorem actual_anchor_tail_extension (n h k : ℕ) (a : Fin (n+1) → ℂ)
    (c : ℂ) (hh : h ≤ k) (hk : k ≤ n) (initial : Fin (h+1) → ℂ)
    (hprefix : ∀ i, (ordinaryRow a (i.val+1)).eval (initial i)=0) :
    ∃ z : Fin (k+1) → ℂ,
      (∀ i, (ordinaryRow a (i.val+1)).eval (z i)=0) ∧
      (∀ i, z (Fin.castLE (Nat.succ_le_succ hh) i)=initial i) ∧
      chainCost z+‖z (Fin.last k)-c‖ ≤ chainCost initial+‖initial (Fin.last h)-c‖+
        2*(∑ m ∈ Finset.Icc (h+2) (k+1), anchorRadius a c m) := by
  classical
  induction k, hh using Nat.le_induction with
  | base =>
    refine ⟨initial,hprefix,?_,?_⟩
    · intro i; rfl
    · simp
  | succ k hh ih =>
    obtain ⟨z,hz,hext,hcost⟩ := ih (by omega)
    obtain ⟨w,hw,hη⟩ := exists_actual_root_anchor (ordinaryRow a (k+2))
      (ordinaryRow_monic a (by omega)) (k+2) (by omega)
      (ordinaryRow_natDegree a (by omega)) c
    change ‖w-c‖ ≤ anchorRadius a c (k+2) at hη
    refine ⟨Fin.snoc z w,?_,?_,?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last,Fin.val_last] using hw
      | cast i => simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hz i
    · intro i
      have he : (Fin.castLE (by omega : h+1 ≤ k+2) i : Fin (k+2)) =
          (Fin.castLE (Nat.succ_le_succ hh) i).castSucc := by ext; rfl
      rw [he,Fin.snoc_castSucc]
      exact hext i
    · have ht : ‖w-z (Fin.last k)‖ ≤ ‖w-c‖+‖z (Fin.last k)-c‖ := by
        have ht := norm_add_le (w-c) (c-z (Fin.last k))
        rw [sub_add_sub_cancel] at ht
        simpa only [norm_sub_rev c (z (Fin.last k))] using ht
      rw [complex_chainCost_snoc,Fin.snoc_last,Finset.sum_Icc_succ_top (by omega)]
      linarith

theorem actual_complete_chain_from_prefix (n h : ℕ) (a : Fin (n+1) → ℂ)
    (c : ℂ) (hh : h ≤ n) (initial : Fin (h+1) → ℂ)
    (hprefix : ∀ i, (ordinaryRow a (i.val+1)).eval (initial i)=0) :
    ∃ z : Fin (n+1) → ℂ, IsChain a z ∧
      (∀ i, z (Fin.castLE (Nat.succ_le_succ hh) i)=initial i) ∧
      chainCost z ≤ chainCost initial+‖initial (Fin.last h)-c‖+
        2*(∑ m ∈ Finset.Icc (h+2) (n+1), anchorRadius a c m) := by
  obtain ⟨z,hz,hext,hcost⟩ := actual_anchor_tail_extension n h n a c hh le_rfl initial hprefix
  refine ⟨z,?_,hext,?_⟩
  · intro i
    have ht := (ordinaryRow_eval_zero_iff a (z i)).mp (hz i)
    simpa only [DerivativeChainPrivate.IsChain,row,fromRoots,sourcePolynomial] using ht
  · linarith [norm_nonneg (z (Fin.last n)-c)]

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









theorem uniform_tower_variance_contraction (r : ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (hh : h ≤ n) :
    (n:ℝ)*(∑ j : Fin (h+1), (h+1:ℝ)⁻¹*‖r h j-r 0 0‖^2) ≤
      (h:ℝ)*(∑ j : Fin (n+1), (n+1:ℝ)⁻¹*‖r n j-r 0 0‖^2) := by
  have hs (k : ℕ) (hk : k<n) :
      (k+1:ℝ)*secondMoment (fun j : Fin (k+1) => r k j-r 0 0) ≤
        (k:ℝ)*secondMoment (fun i : Fin (k+2) => r (k+1) i-r 0 0) :=
    uniform_step_variance_contraction r k (hstep k hk) (r 0 0)
      (uniform_row_centroid r n hstep (k+1) (by omega))
  have H := scaled_sequence_contraction
    (fun k => secondMoment (fun i : Fin (k+1) => r k i-r 0 0)) n h hh hs
  simpa only [secondMoment,Complex.normSq_eq_norm_sq,div_eq_mul_inv,
    Finset.mul_sum,Finset.sum_mul,mul_comm,Nat.cast_add,Nat.cast_one] using H

theorem uniform_tower_variance_contraction_div (r : ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (hh : h ≤ n) :
    (∑ j : Fin (h+1), (h+1:ℝ)⁻¹*‖r h j-r 0 0‖^2) ≤
      (h:ℝ)/(n:ℝ)*(∑ j : Fin (n+1), (n+1:ℝ)⁻¹*‖r n j-r 0 0‖^2) := by
  by_cases hn : n=0
  · subst n
    have he : h=0 := by omega
    subst h
    simp
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hnR).2
  simpa only [mul_comm] using uniform_tower_variance_contraction r n h hstep hh

end
end DerivativeChainPrefixLaws


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
namespace DerivativeChainClusterAnchor
noncomputable section

theorem source_tower_prefix_reserve (r : ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (hh : h ≤ n) (c : ℂ) :
    ∃ z : Fin (h+1) → ℂ, IsComplexRowHistory r z ∧
      chainCost z+‖z (Fin.last h)-c‖ ≤
        (h:ℝ)*Real.sqrt (rowCenteredVariance r n (r 0 0)/(n:ℝ))+
          Real.sqrt ((h:ℝ)*rowCenteredVariance r n (r 0 0)/(n:ℝ)+‖r 0 0-c‖^2) := by
  obtain ⟨z,hz,hcost⟩ := joint_complete_prefix_reserve r h (fun k hk => hstep k (by omega)) c
  have hv : rowCenteredVariance r h (r 0 0) ≤
      (h:ℝ)/(n:ℝ)*rowCenteredVariance r n (r 0 0) := by
    simpa only [rowCenteredVariance] using uniform_tower_variance_contraction_div r n h hstep hh
  have hV : 0 ≤ rowCenteredVariance r n (r 0 0) := by unfold rowCenteredVariance; positivity
  have hscaled : (h:ℝ)*rowCenteredVariance r h (r 0 0) ≤
      (h:ℝ)^2*(rowCenteredVariance r n (r 0 0)/(n:ℝ)) := by
    have ht := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg h)
    exact ht.trans_eq (by ring)
  have hA : Real.sqrt ((h:ℝ)*rowCenteredVariance r h (r 0 0)) ≤
      (h:ℝ)*Real.sqrt (rowCenteredVariance r n (r 0 0)/(n:ℝ)) := by
    have ht := Real.sqrt_le_sqrt hscaled
    rw [Real.sqrt_mul (sq_nonneg (h:ℝ)),Real.sqrt_sq (Nat.cast_nonneg h)] at ht
    exact ht
  have hC : Real.sqrt (rowCenteredVariance r h (r 0 0)+‖r 0 0-c‖^2) ≤
      Real.sqrt ((h:ℝ)*rowCenteredVariance r n (r 0 0)/(n:ℝ)+‖r 0 0-c‖^2) := by
    apply Real.sqrt_le_sqrt
    have he : (h:ℝ)/(n:ℝ)*rowCenteredVariance r n (r 0 0)=
        (h:ℝ)*rowCenteredVariance r n (r 0 0)/(n:ℝ) := by ring
    rw [he] at hv
    exact add_le_add hv le_rfl
  exact ⟨z,hz,hcost.trans (add_le_add hA hC)⟩

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
open DerivativeChainClusterAnchor






theorem solution (n r : ℕ) (a : Fin (n+1) → ℂ) (c : ℂ)
    (O : Finset (Fin (n+1))) (hr : 0 < r) (hcut : 2*r < n+1) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D) :
    let u := _root_.DerivativeChainContinuation.complexCentroid a
    let V := ∑ i, (n+1:ℝ)⁻¹*‖a i-u‖^2
    ∃ z : Fin (n+1) → ℂ, _root_.DerivativeChainPrivate.IsChain a z ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ ((2*r-1:ℕ):ℝ)*Real.sqrt (V/(n:ℝ))+
        Real.sqrt (((2*r-1:ℕ):ℝ)*V/(n:ℝ)+‖u-c‖^2)+
        4*(n+1:ℝ)*ε+16*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (D*ε/(n+1:ℝ)) := by
  dsimp only
  obtain ⟨rows,htop,hstep⟩ := _root_.DerivativeChainContinuation.uniform_polynomial_tower n a
  let h : ℕ := 2*r-1
  have hh : h ≤ n := by dsimp [h]; omega
  obtain ⟨initial,hprefix,hbound⟩ := _root_.DerivativeChainClusterAnchor.source_tower_prefix_reserve rows n h hstep hh c
  obtain ⟨z,hz,_,hjoin⟩ := _root_.DerivativeChainClusterAnchor.actual_complete_chain_from_prefix n h a c hh initial
    (_root_.DerivativeChainClusterAnchor.complex_history_ordinary_prefix n h a rows htop hstep hh initial hprefix)
  have hcent : _root_.DerivativeChainContinuation.complexCentroid a=rows 0 0 := by
    simpa only [htop] using _root_.DerivativeChainPrefixLaws.uniform_row_centroid rows n hstep n le_rfl
  have hV : _root_.DerivativeChainClusterAnchor.rowCenteredVariance rows n (rows 0 0)=
      ∑ i, (n+1:ℝ)⁻¹*‖a i-_root_.DerivativeChainContinuation.complexCentroid a‖^2 := by
    simp only [_root_.DerivativeChainClusterAnchor.rowCenteredVariance,htop,hcent]
  rw [hV,← hcent] at hbound
  have hindex : h+2=2*r+1 := by dsimp [h]; omega
  rw [hindex] at hjoin
  have htail := _root_.DerivativeChainClusterAnchor.source_cluster_tail_bound_full a c O hr hcut hO ε D hε hnear hall
  refine ⟨z,hz,?_⟩
  dsimp [h] at hbound hjoin
  norm_num only [Nat.cast_add,Nat.cast_one] at htail
  nlinarith
