-- Prove2me | solution 1 for DerivativeChainClusterAnchor.majority_atom_array
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:58:29.853611+00:00
-- url     : https://prove2.me/submissions/ff612d4d-0861-4b7a-b336-b7fb2cc10b8e

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_baseline_complete_chain_radius
import Theorems.Thm_DerivativeChainClusterAnchor_cluster_source_centroid_variance
import Theorems.Thm_DerivativeChainClusterAnchor_exact_atom_history_budget
import Theorems.Thm_DerivativeChainClusterAnchor_majority_atom_scalar_budget
import Theorems.Thm_DerivativeChainClusterAnchor_majority_atom_source_variance
import Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_eval_zero_of_exact_cluster
import Theorems.Thm_DerivativeChainPrefixLaws_source_uniform_variance_controlled_tower
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
set_option maxHeartbeats 1500000
namespace DerivativeChainClusterAnchor

theorem cube_fraction_bound (N q k C : ℝ) (hN : 0 < N) (hq : 0 ≤ q) (hk : 0 < k)
    (hcube : C*q^3 ≤ N^2) (hscale : k^3 ≤ C*N) : k*q ≤ N := by
  by_contra h
  have hlt : N < k*q := lt_of_not_ge h
  have hx : 0 < k*q := hN.trans hlt
  have h1 := mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hN)
  have h2 := mul_lt_mul_of_pos_right hlt (mul_pos hx hN)
  have h3 := mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hx)
  have hu1 := mul_le_mul_of_nonneg_right hscale (pow_nonneg hq 3)
  have hu2 := mul_le_mul_of_nonneg_left hcube hN.le
  nlinarith





end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainPrivate
namespace DerivativeChainClusterAnchor
noncomputable section

theorem zero_radius_complete_chain {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) (o : ℂ)
    (hall : ∀ i, ‖a i-o‖ ≤ 0) :
    ∃ z : Fin n → ℂ, DerivativeChainPrivate.IsChain a z ∧ chainCost z=0 := by
  have ha (i : Fin n) : a i=o := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (hall i) (norm_nonneg _)))
  refine ⟨(fun _ => o),?_,?_⟩
  · intro i
    have hh := ordinaryRow_eval_zero_of_exact_cluster a o ∅ (by omega : i.val+1 ≤ n)
      (by simp : (∅ : Finset (Fin n)).card ≤ 0) (by omega : 0 < i.val+1) (fun j _ => ha j)
    have hr := (ordinaryRow_eval_zero_iff a o).mp hh
    simpa only [row,fromRoots,sourcePolynomial] using hr
  · simp [chainCost]



end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainPrefixLaws
noncomputable section

theorem uniform_row_sum (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    (∑ j : Fin (h+1), r h j)=(h+1:ℂ)*r 0 0 := by
  have hc := uniform_row_centroid r n hstep h hh
  have hn : (h+1:ℂ) ≠ 0 := by exact_mod_cast (show h+1 ≠ 0 by omega)
  have hs := (div_eq_iff hn).mp hc
  simpa only [mul_comm] using hs

theorem uniform_row_weighted_mean (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    (∑ j : Fin (h+1), (((h+1:ℝ)⁻¹:ℝ):ℂ)*r h j)=r 0 0 := by
  rw [← Finset.mul_sum,uniform_row_sum r n hstep h hh]
  have hn : (h+1:ℂ) ≠ 0 := by exact_mod_cast (show h+1 ≠ 0 by omega)
  push_cast
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]





end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
namespace DerivativeChainClusterAnchor
noncomputable section

theorem source_mean_identity (n : ℕ) (a : Fin (n+1) → ℂ) :
    (∑ i, (((n+1:ℝ)⁻¹:ℝ):ℂ)*a i)=complexCentroid a := by
  obtain ⟨rows,htop,hstep,hcent,_⟩ := source_uniform_variance_controlled_tower n a
  simpa only [htop,hcent] using uniform_row_weighted_mean rows n hstep n le_rfl













end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor


theorem solution (n r : ℕ) (a : Fin (n+1) → ℂ) (o c : ℂ)
    (O : Finset (Fin (n+1))) (R : ℝ) (hcube : r^3 ≤ (n+1)^2) (hO : O.card ≤ r)
    (hR : 0 ≤ R) (hsource : ∀ i, ‖a i-o‖ ≤ R) (hc : ∃ i, a i=c)
    (hnear : ∀ i, i ∉ O → a i=c) :
    ∃ z : Fin (n+1) → ℂ, _root_.DerivativeChainPrivate.IsChain a z ∧ _root_.DerivativeChainPrivate.chainCost z ≤ (2+Real.sqrt 2)*R := by
  classical
  have hcR : ‖c-o‖ ≤ R := by obtain ⟨i,hi⟩ := hc; rw [← hi]; exact hsource i
  cases r with
  | zero =>
    have he : O=∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hO)
    have hall0 (i : Fin (n+1)) : ‖a i-c‖ ≤ 0 := by simp [hnear i (by simp [he])]
    obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.zero_radius_complete_chain (by omega : 0 < n+1) a c hall0
    exact ⟨z,hz,by rw [hcost]; positivity⟩
  | succ t =>
    have hr : 0 < t+1 := by omega
    by_cases hnsmall : n+1 < 8
    · obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.baseline_complete_chain_radius (by omega : 0 < n+1) a o R hR hsource
      have hcost' : _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt (n:ℝ)*R := by simpa only [Nat.add_sub_cancel] using hcost
      have hnR : (n:ℝ) ≤ 6 := by exact_mod_cast (by omega : n ≤ 6)
      have hroot : Real.sqrt (n:ℝ) ≤ 2+Real.sqrt 2 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
      exact ⟨z,hz,hcost'.trans (mul_le_mul_of_nonneg_right hroot hR)⟩
    · have hn8 : 8 ≤ n+1 := by omega
      have hnR : (8:ℝ) ≤ n+1 := by exact_mod_cast hn8
      have hrR : (0:ℝ) < t+1 := by positivity
      have hcubR : (t+1:ℝ)^3 ≤ (n+1:ℝ)^2 := by exact_mod_cast hcube
      have hfrac := _root_.DerivativeChainClusterAnchor.cube_fraction_bound (n+1:ℝ) (t+1:ℝ) 2 1 (by linarith) hrR.le (by norm_num)
        (by simpa only [one_mul] using hcubR) (by nlinarith)
      have hhalf : 2*(t+1) ≤ n+1 := by exact_mod_cast hfrac
      have hrlt : t+1 < n+1 := by omega
      have hmean := _root_.DerivativeChainClusterAnchor.source_mean_identity n a
      have hsharp := _root_.DerivativeChainClusterAnchor.majority_atom_source_variance a c o (_root_.DerivativeChainContinuation.complexCentroid a) O (by omega) hO hhalf
        R hR hcR hsource hnear (by simpa only [Nat.cast_add,Nat.cast_one] using hmean)
      norm_num only [Nat.cast_add,Nat.cast_one] at hsharp
      have hcross (i : Fin (n+1)) : ‖a i-c‖ ≤ 2*R := by
        have ht : ‖a i-c‖ ≤ ‖a i-o‖+‖o-c‖ := by simpa only [dist_eq_norm] using dist_triangle (a i) o c
        have hc' : ‖o-c‖ ≤ R := by simpa only [norm_sub_rev] using hcR
        linarith [hsource i]
      have hnear0 (i : Fin (n+1)) (hi : i ∉ O) : ‖a i-c‖ ≤ 0 := by simp [hnear i hi]
      have hm0 := _root_.DerivativeChainClusterAnchor.cluster_source_centroid_variance a c (_root_.DerivativeChainContinuation.complexCentroid a) O (by omega) hO
        0 (2*R) (by norm_num) (by positivity) hnear0 hcross
        (by simpa only [Nat.cast_add,Nat.cast_one] using hmean)
      norm_num only [Nat.cast_add,Nat.cast_one,zero_add] at hm0
      let V := ∑ i, (n+1:ℝ)⁻¹*‖a i-_root_.DerivativeChainContinuation.complexCentroid a‖^2
      let δ := ‖_root_.DerivativeChainContinuation.complexCentroid a-c‖
      have hδ : δ ≤ 2*((t+1:ℝ)/(n+1:ℝ))*R := hm0.2.trans_eq (by ring)
      obtain ⟨z,hz,_,hcost⟩ := _root_.DerivativeChainClusterAnchor.exact_atom_history_budget n t a c O hrlt hO hnear
      have hs := _root_.DerivativeChainClusterAnchor.majority_atom_scalar_budget (n+1) (t+1) hn8 hr hcube R V δ hR
        (by dsimp [V]; positivity) (norm_nonneg _)
        (by simpa only [V,Nat.cast_add,Nat.cast_one] using hsharp)
        (by simpa only [δ,Nat.cast_add,Nat.cast_one] using hδ)
      change _root_.DerivativeChainPrivate.chainCost z ≤ (t:ℝ)*Real.sqrt (V/(n:ℝ))+
        Real.sqrt ((t:ℝ)*V/(n:ℝ)+δ^2) at hcost
      norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hs
      exact ⟨z,hz,hcost.trans hs⟩
