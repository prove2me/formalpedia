-- Prove2me | solution 1 for DerivativeChainContinuation.at_most_two_centered_modes_chain
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:04:21.438979+00:00
-- url     : https://prove2.me/submissions/4a438111-5366-455a-b500-d8fbb5784aec

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_AppellTranslation
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainContinuation_TwoModeChain
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_appell_no_return_disk_bound
import Theorems.Thm_DerivativeChainContinuation_sparse_cluster_chain_bound
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial





theorem centeredSource_roots (p : Polynomial ℂ) :
    (centeredSource p).roots = p.roots.map (fun z => z-rootCentroid p) := by
  simpa [centeredSource] using
    (roots_comp_C_mul_X_add_C p 1 (rootCentroid p) isUnit_one)

theorem centeredSource_natDegree (p : Polynomial ℂ) :
    (centeredSource p).natDegree = p.natDegree := by
  rw [centeredSource, natDegree_comp, natDegree_X_add_C, mul_one]

theorem centeredSource_monic (p : Polynomial ℂ) (hp : p.Monic) :
    (centeredSource p).Monic := hp.comp_X_add_C _

theorem centeredSource_centered (p : Polynomial ℂ) (hn : p.natDegree ≠ 0) :
    (centeredSource p).roots.sum = 0 := by
  rw [centeredSource_roots]
  have hc := splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hnC : (p.natDegree : ℂ) ≠ 0 := by exact_mod_cast hn
  simp [Multiset.sum_map_sub, hc, rootCentroid, nsmul_eq_mul]
  field_simp [hnC]
  ring




end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem appellRow_coeff (m k : ℕ) (c : ℕ → ℂ) :
    (appellRow m c).coeff k = if k ≤ m then (m.choose k:ℂ)*c (m-k) else 0 := by
  classical
  simp only [appellRow,finsetSum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  simp [Finset.sum_ite_eq',Nat.lt_succ_iff]

theorem appellRow_coeff_eq (m k : ℕ) (c : ℕ → ℂ) :
    (appellRow m c).coeff k = (m.choose k:ℂ)*c (m-k) := by
  rw [appellRow_coeff]
  split_ifs with hk
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]











end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial





theorem translatedAppell_eval (m : ℕ) (c : ℕ → ℂ) (u z : ℂ) :
    (translatedAppell m c u).eval z=(appellRow m c).eval (z-u) := by
  simp [translatedAppell]





end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



theorem appellCoefficients_zero (p : Polynomial ℂ) (hp : p.Monic) :
    appellCoefficients p 0=1 := by
  simpa [appellCoefficients] using hp.leadingCoeff

theorem appellRow_coefficients (p : Polynomial ℂ) :
    appellRow p.natDegree (appellCoefficients p)=p := by
  ext k
  rw [appellRow_coeff_eq]
  by_cases hk : k ≤ p.natDegree
  · have hn : (p.natDegree.choose k:ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hk
    unfold appellCoefficients
    rw [Nat.sub_sub_self hk,Nat.choose_symm hk]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem translatedAppell_centeredSource (p : Polynomial ℂ) :
    (appellRow p.natDegree (appellCoefficients (centeredSource p))).comp (X-C (rootCentroid p))=p := by
  rw [← centeredSource_natDegree p,appellRow_coefficients,centeredSource,comp_assoc]
  have he : (X+C (rootCentroid p)).comp (X-C (rootCentroid p)) = (X:Polynomial ℂ) := by simp
  rw [he,comp_X]

end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

theorem appellCoefficients_one (p : Polynomial ℂ) (hp : p.Monic)
    (hn : 0 < p.natDegree) (hc : p.roots.sum=0) : appellCoefficients p 1=0 := by
  have ht := (IsAlgClosed.splits p).nextCoeff_eq_neg_sum_roots_of_monic hp
  rw [hc,neg_zero,nextCoeff_of_natDegree_pos hn] at ht
  simp only [appellCoefficients,ht,zero_div]

end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate

theorem two_centered_modes_chain_bound (p : Polynomial ℂ) (hp : p.Monic) (n q r : ℕ)
    (hn : p.natDegree=n) (hq : 2 ≤ q) (hqr : q < r) (hrn : r ≤ n)
    (hsupport : ∀ j ≤ n, 2 ≤ j → j ≠ q → j ≠ r → (centeredSource p).coeff (n-j)=0)
    (a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧
      chainCost z ≤ (1+Real.sqrt 2)*Real.sqrt (D^2-‖rootCentroid p-a‖^2) := by
  have hs : ∀ j ≤ n, 2 ≤ j → j ≠ q → (j ≤ r-1 ∨ r < j) →
      (centeredSource p).coeff (n-j)=0 := by
    intro j hj hj2 hjq hjr
    exact hsupport j hj hj2 hjq (by omega)
  obtain ⟨z,hzr,hz0,_,hzc,_⟩ := sparse_cluster_chain_bound p hp n r 1 q hn (by norm_num)
    hq (by omega) hrn hs a D hD hbound
  refine ⟨z,hzr,hz0,hzc.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  split_ifs <;> norm_num <;> linarith



end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hn : p.natDegree=n) (hnpos : 0 < n)
    (hmodes : (centeredModeSupport p).card ≤ 2)
    (a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ z : ℂ, p.eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,hnpos⟩=rootCentroid p ∧
      chainCost z ≤ (1+Real.sqrt 2)*Real.sqrt (D^2-‖rootCentroid p-a‖^2) := by
  classical
  let c := appellCoefficients (centeredSource p)
  have hc0 : c 0=1 := appellCoefficients_zero _ (centeredSource_monic p hp)
  have hc1 : c 1=0 := appellCoefficients_one _ (centeredSource_monic p hp)
    (by rw [centeredSource_natDegree,hn]; exact hnpos) (centeredSource_centered p (by omega))
  have hsrc : translatedAppell n c (rootCentroid p)=p := by
    simpa only [translatedAppell,hn,c] using translatedAppell_centeredSource p
  by_cases hn1 : n=1
  · subst hn1
    have hu : p.eval (rootCentroid p)=0 := by
      have hu' : (translatedAppell 1 c (rootCentroid p)).eval (rootCentroid p)=0 := by
        rw [translatedAppell_eval,sub_self,← coeff_zero_eq_eval_zero,appellRow_coeff_eq]
        simpa using hc1
      rwa [hsrc] at hu' 
    refine ⟨fun _ => rootCentroid p,?_,rfl,?_⟩
    · intro i
      rw [show 1-(i.val+1)=0 by omega,Function.iterate_zero_apply]
      exact hu
    · simp only [chainCost,sub_self,norm_zero,Finset.sum_const_zero]
      positivity
  by_cases hn2 : n=2
  · subst hn2
    have hpref : ∀ j ≤ 2, j ≠ 0 → j ≠ 2 → c j=0 := by
      intro j hj hj0 hj2
      have hj1 : j=1 := by omega
      rwa [hj1]
    have hdisk (w : ℂ) (hw : (translatedAppell (2+0) c (rootCentroid p)).eval w=0) : ‖w-a‖ ≤ D := by
      rw [hsrc] at hw
      exact hbound w hw
    obtain ⟨z,hzr,hz0,hzc,_⟩ := appell_no_return_disk_bound 2 0 2 (by norm_num) (by norm_num)
      c hc0 hpref (rootCentroid p) a D hD hdisk
    refine ⟨z,?_,hz0,?_⟩
    · simpa only [Nat.add_zero,hsrc] using hzr
    · have hh : chainCost z ≤ Real.sqrt (D^2-‖rootCentroid p-a‖^2) := by simpa using hzc
      have hm := mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (D^2-‖rootCentroid p-a‖^2))
      nlinarith
  have hn3 : 3 ≤ n := by omega
  let S := (Finset.Icc 2 n).filter (fun j => (centeredSource p).coeff (n-j) ≠ 0)
  have hScard : S.card ≤ 2 := by simpa only [centeredModeSupport,hn] using hmodes
  have hSsub : S ⊆ Finset.Icc 2 n := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hIcard : 2 ≤ (Finset.Icc 2 n).card := by rw [Nat.card_Icc]; omega
  obtain ⟨T,hST,hTI,hTcard⟩ := Finset.exists_subsuperset_card_eq hSsub hScard hIcard
  obtain ⟨q,r,hne,hTeq⟩ := Finset.card_eq_two.mp hTcard
  have hqm : q ∈ Finset.Icc 2 n := hTI (by rw [hTeq]; simp)
  have hrm : r ∈ Finset.Icc 2 n := hTI (by rw [hTeq]; simp)
  obtain ⟨hq2,hqn⟩ := Finset.mem_Icc.mp hqm
  obtain ⟨hr2,hrn⟩ := Finset.mem_Icc.mp hrm
  have hzero (j : ℕ) (hjn : j ≤ n) (hj2 : 2 ≤ j) (hjq : j ≠ q) (hjr : j ≠ r) :
      (centeredSource p).coeff (n-j)=0 := by
    by_contra hz
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj2,hjn⟩,hz⟩
    have ht := hST hjS
    rw [hTeq] at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with ht|ht
    · exact hjq ht
    · exact hjr ht
  by_cases hqr : q < r
  · exact two_centered_modes_chain_bound p hp n q r hn hq2 hqr hrn hzero a D hD hbound
  · exact two_centered_modes_chain_bound p hp n r q hn hr2 (by omega) hqn
      (fun j hj hj2 hjr hjq => hzero j hj hj2 hjq hjr) a D hD hbound
