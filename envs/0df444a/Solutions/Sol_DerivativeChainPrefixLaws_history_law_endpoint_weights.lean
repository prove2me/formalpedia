-- Prove2me | solution 1 for DerivativeChainPrefixLaws.history_law_endpoint_weights
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:46:20.044808+00:00
-- url     : https://prove2.me/submissions/b0b7f08b-a712-48db-ad45-2da8a4e8e806

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrefixLaws_linear_row_root_eq_centroid
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainPrefixLaws
noncomputable section































theorem endpoint_cost_nonneg {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ) :
    0 ≤ complexEndpointCost a v := by
  apply Real.sInf_nonneg
  rintro t ⟨z,hz,he,rfl⟩
  unfold chainCost
  positivity

theorem endpoint_cost_le_chain {n : ℕ} (a : Fin (n+1) → ℂ) (z : Fin (n+1) → ℂ)
    (hz : IsChain a z) : complexEndpointCost a (z (Fin.last n)) ≤ chainCost z := by
  unfold complexEndpointCost
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro t ⟨zz,hzz,he,rfl⟩
    unfold chainCost
    positivity
  · exact ⟨z,hz,rfl,rfl⟩

end
end DerivativeChainPrefixLaws


section

set_option autoImplicit false
open scoped BigOperators
open DerivativeChainPrivate
universe v
namespace DerivativeChainFiniteHistory







theorem FiniteBalancedHistoryLaw.centroid_root {n : ℕ} {a : Fin (n+1) → ℂ}
    {u : ℂ} {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw a u κ) :
    (row a 1).eval u = 0 := by
  classical
  have hne : (∑ i, L.weights i) ≠ 0 := by rw [L.total]; exact one_ne_zero
  obtain ⟨i, _⟩ := Finset.nonempty_of_sum_ne_zero hne
  have h := L.actual i 0
  change (row a 1).eval (L.paths i 0) = 0 at h
  rwa [L.start i] at h





end DerivativeChainFiniteHistory


end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainFiniteHistory
universe v
namespace DerivativeChainPrefixLaws
noncomputable section

theorem chain_endpoint_slot {n : ℕ} (a : Fin (n+1) → ℂ) (z : Fin (n+1) → ℂ)
    (hz : IsChain a z) : ∃ j, z (Fin.last n)=a j := by
  have he : (∏ j, (z (Fin.last n)-a j))=0 := by
    simpa only [row,Fin.val_last,Nat.sub_self,Function.iterate_zero_apply,fromRoots,
      eval_prod,eval_sub,eval_X,eval_C] using hz (Fin.last n)
  obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp he
  exact ⟨j,sub_eq_zero.mp hj⟩







end
end DerivativeChainPrefixLaws


end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainFiniteHistory
universe v
open DerivativeChainPrefixLaws




theorem solution {n : ℕ} {a : Fin (n+1) → ℂ} {u : ℂ}
    {κ : Type v} [Fintype κ] (L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a u κ) :
    ∃ W : Fin (n+1) → ℝ, _root_.DerivativeChainPrefixLaws.BalancedWeights a (_root_.DerivativeChainContinuation.complexCentroid a) W ∧
      _root_.DerivativeChainPrefixLaws.rootLawVariance a W=L.endpointVariance ∧ _root_.DerivativeChainPrefixLaws.rootLawSquareCost a W ≤ L.meanSquareCost := by
  classical
  have hu : u=_root_.DerivativeChainContinuation.complexCentroid a := _root_.DerivativeChainPrefixLaws.linear_row_root_eq_centroid a u L.centroid_root
  subst u
  have hslot (i : κ) : ∃ j, L.paths i (Fin.last n)=a j :=
    _root_.DerivativeChainPrefixLaws.chain_endpoint_slot a (L.paths i) (L.actual i)
  let last : κ → Fin (n+1) := fun i => Classical.choose (hslot i)
  have hend (i : κ) : L.paths i (Fin.last n)=a (last i) := Classical.choose_spec (hslot i)
  let W : Fin (n+1) → ℝ := fun j => ∑ i, if last i=j then L.weights i else 0
  have hpush (f : Fin (n+1) → ℝ) :
      (∑ j,W j*f j)=∑ i,L.weights i*f (last i) := by
    simp only [W,Finset.sum_mul,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hw0 (j : Fin (n+1)) : 0 ≤ W j := by
    dsimp [W]
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact L.nonneg i
    · exact le_rfl
  have hws : (∑ j,W j)=1 := by
    simpa only [mul_one,L.total] using hpush (fun _ => 1)
  have hwr : (∑ j,W j*(a j).re)=(_root_.DerivativeChainContinuation.complexCentroid a).re := by
    have hl := congrArg Complex.re L.balanced
    simp_rw [hend] at hl
    have hl' : (∑ i,L.weights i*(a (last i)).re)=(_root_.DerivativeChainContinuation.complexCentroid a).re := by
      simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero] using hl
    exact (hpush (fun j => (a j).re)).trans hl'
  have hwi : (∑ j,W j*(a j).im)=(_root_.DerivativeChainContinuation.complexCentroid a).im := by
    have hl := congrArg Complex.im L.balanced
    simp_rw [hend] at hl
    have hl' : (∑ i,L.weights i*(a (last i)).im)=(_root_.DerivativeChainContinuation.complexCentroid a).im := by
      simpa only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,add_zero] using hl
    exact (hpush (fun j => (a j).im)).trans hl'
  have hwm : (∑ j,(W j:ℂ)*a j)=_root_.DerivativeChainContinuation.complexCentroid a := by
    apply Complex.ext
    · simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero] using hwr
    · simpa only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,add_zero] using hwi
  have hvar : _root_.DerivativeChainPrefixLaws.rootLawVariance a W=L.endpointVariance := by
    unfold _root_.DerivativeChainPrefixLaws.rootLawVariance _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.endpointVariance
    simp_rw [hend]
    exact hpush (fun j => ‖a j-_root_.DerivativeChainContinuation.complexCentroid a‖^2)
  have hcost : _root_.DerivativeChainPrefixLaws.rootLawSquareCost a W ≤ L.meanSquareCost := by
    unfold _root_.DerivativeChainPrefixLaws.rootLawSquareCost _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.meanSquareCost
    rw [hpush (fun j => (_root_.DerivativeChainContinuation.complexEndpointCost a (a j))^2)]
    apply Finset.sum_le_sum
    intro i _
    have hc0 := _root_.DerivativeChainPrefixLaws.endpoint_cost_nonneg a (L.paths i (Fin.last n))
    have hc := _root_.DerivativeChainPrefixLaws.endpoint_cost_le_chain a (L.paths i) (L.actual i)
    have hz0 : 0 ≤ _root_.DerivativeChainPrivate.chainCost (L.paths i) := by unfold _root_.DerivativeChainPrivate.chainCost; positivity
    have hs := (sq_le_sq₀ hc0 hz0).2 hc
    rw [hend i] at hs
    exact mul_le_mul_of_nonneg_left hs (L.nonneg i)
  exact ⟨W,⟨hw0,hws,hwm⟩,hvar,hcost⟩
