-- Prove2me | solution 1 for DerivativeChainPhaseLock.large_gain_actual_extension
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:51:01.743305+00:00
-- url     : https://prove2.me/submissions/5d2446a2-e871-4fb3-b9a7-32e7a32a4a27

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
import Definitions.Def_DerivativeChainAnalytic_BarycentricMoments
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPhaseLock_actual_kernel_extension
import Theorems.Thm_DerivativeChainPhaseLock_kernel_edge_energy
import Theorems.Thm_DerivativeChainPhaseLock_kernel_rms_bound
import Theorems.Thm_DerivativeChainPhaseLock_large_gain_rms_budget
import Theorems.Thm_DerivativeChainPrefixLaws_history_law_endpoint_weights
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

























theorem weighted_cost_difference {n : ℕ} (a : Fin (n+1) → ℂ)
    (w : Fin (n+1) → ℝ) (K : ℝ) :
    (∑ i,w i*((complexEndpointCost a (a i))^2-K*‖a i-complexCentroid a‖^2))=
      rootLawSquareCost a w-K*rootLawVariance a w := by
  simp only [rootLawSquareCost,rootLawVariance,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem bellman_objectives_bddBelow {n : ℕ} (a : Fin (n+1) → ℂ) (K : ℝ) :
    BddBelow {q | ∃ w : Fin (n+1) → ℝ, BalancedWeights a (complexCentroid a) w ∧
      q=rootLawSquareCost a w-K*rootLawVariance a w} := by
  classical
  let f : Fin (n+1) → ℝ := fun i => (complexEndpointCost a (a i))^2-K*‖a i-complexCentroid a‖^2
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨f j,?_⟩
  rintro q ⟨w,hw,rfl⟩
  rw [← weighted_cost_difference]
  calc
    f j = ∑ i,w i*f j := by rw [← Finset.sum_mul,hw.2.1,one_mul]
    _ ≤ ∑ i,w i*f i := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hj i (Finset.mem_univ i)) (hw.1 i))

theorem bellmanValue_nonpos_of_weights {n : ℕ} (a : Fin (n+1) → ℂ) (w : Fin (n+1) → ℝ)
    (hw : BalancedWeights a (complexCentroid a) w) (K : ℝ)
    (hcost : rootLawSquareCost a w ≤ K*rootLawVariance a w) : bellmanValue a K ≤ 0 := by
  have hm : rootLawSquareCost a w-K*rootLawVariance a w ∈
      {q | ∃ w : Fin (n+1) → ℝ, BalancedWeights a (complexCentroid a) w ∧
        q=rootLawSquareCost a w-K*rootLawVariance a w} := ⟨w,hw,rfl⟩
  exact (csInf_le (bellman_objectives_bddBelow a K) hm).trans (sub_nonpos.mpr hcost)





end
end DerivativeChainPrefixLaws


section

set_option autoImplicit false
open scoped BigOperators
open DerivativeChainPrivate
universe v
namespace DerivativeChainFiniteHistory









theorem FiniteBalancedHistoryLaw.meanSquareCost_nonneg {n : ℕ} {a : Fin (n+1) → ℂ}
    {u : ℂ} {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw a u κ) :
    0 ≤ L.meanSquareCost := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (L.nonneg i) (sq_nonneg _)

theorem FiniteBalancedHistoryLaw.endpointVariance_nonneg {n : ℕ} {a : Fin (n+1) → ℂ}
    {u : ℂ} {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw a u κ) :
    0 ≤ L.endpointVariance := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (L.nonneg i) (sq_nonneg _)

end DerivativeChainFiniteHistory


end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
universe v
namespace DerivativeChainPhaseLock
noncomputable section











theorem actual_barycentric_extension {n : ℕ} (a : Fin (n+2) → ℂ) (b : Fin (n+1) → ℂ)
    (u : ℂ) {κ : Type v} [Fintype κ]
    (hderiv : (fromRoots a).derivative=C (n+2:ℂ)*fromRoots b)
    (L : FiniteBalancedHistoryLaw b u κ)
    (α : κ → (fromRoots a).roots.toFinset → ℝ)
    (hα : ∀ i j, 0 ≤ α i j) (hαsum : ∀ i, ∑ j, α i j=1)
    (hαmean : ∀ i, ∑ j, (α i j:ℂ)*(j:ℂ)=L.paths i (Fin.last n)) :
    ∃ M : FiniteBalancedHistoryLaw a u (κ × (fromRoots a).roots.toFinset),
      (∀ ij,M.weights ij=L.weights ij.1*α ij.1 ij.2) ∧
      (∀ ij,M.paths ij=Fin.snoc (L.paths ij.1) (ij.2:ℂ)) ∧
      M.endpointVariance=parentVariance a L α ∧
      edgeSquareEnergy a L α=M.endpointVariance-L.endpointVariance ∧
      Real.sqrt M.meanSquareCost ≤ Real.sqrt L.meanSquareCost+
        Real.sqrt (M.endpointVariance-L.endpointVariance) := by
  obtain ⟨M,hw,hz,hvar,hcost⟩ := actual_kernel_extension a b u hderiv L α hα hαsum hαmean
  refine ⟨M,hw,hz,hvar,?_,?_⟩
  · rw [hvar]
    exact kernel_edge_energy a L α hαsum hαmean
  · rw [hcost,hvar]
    exact kernel_rms_bound a L α hα hαsum hαmean

end
end DerivativeChainPhaseLock


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







theorem bellmanValue_nonpos_of_history_law {n : ℕ} {a : Fin (n+1) → ℂ} {u : ℂ}
    {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw a u κ) (K : ℝ)
    (hcost : L.meanSquareCost ≤ K*L.endpointVariance) : bellmanValue a K ≤ 0 := by
  obtain ⟨W,hw,hvar,hC⟩ := history_law_endpoint_weights L
  apply bellmanValue_nonpos_of_weights a W hw K
  rw [hvar]
  exact hC.trans hcost

end
end DerivativeChainPrefixLaws


end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainPrefixLaws
universe v
namespace DerivativeChainPhaseLock
noncomputable section

theorem edge_energy_nonneg {n : ℕ} (a : Fin (n+2) → ℂ) {b : Fin (n+1) → ℂ}
    {u : ℂ} {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw b u κ)
    (α : κ → (fromRoots a).roots.toFinset → ℝ) (hα : ∀ i j, 0 ≤ α i j) :
    0 ≤ edgeSquareEnergy a L α := by
  exact Finset.sum_nonneg fun ij _ =>
    mul_nonneg (mul_nonneg (L.nonneg ij.1) (hα ij.1 ij.2)) (sq_nonneg _)







end
end DerivativeChainPhaseLock


end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainPrefixLaws
universe v
open DerivativeChainPhaseLock




theorem solution {n : ℕ} (a : Fin (n+2) → ℂ)
    (b : Fin (n+1) → ℂ) (u : ℂ) {κ : Type v} [Fintype κ]
    (hderiv : (_root_.DerivativeChainPrivate.fromRoots a).derivative=C (n+2:ℂ)*_root_.DerivativeChainPrivate.fromRoots b)
    (L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw b u κ)
    (α : κ → (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → ℝ)
    (hα : ∀ i j, 0 ≤ α i j) (hαsum : ∀ i, ∑ j, α i j=1)
    (hαmean : ∀ i, ∑ j, (α i j:ℂ)*(j:ℂ)=L.paths i (Fin.last n))
    (K : ℝ) (hK : 0 < K) (hchild : L.meanSquareCost ≤ K*L.endpointVariance)
    (hgain : _root_.DerivativeChainPhaseLock.parentVariance a L α=0 ∨
      Real.sqrt (L.endpointVariance/_root_.DerivativeChainPhaseLock.parentVariance a L α) ≤ (K-1)/(K+1)) :
    ∃ M : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a u (κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset),
      (∀ ij,M.weights ij=L.weights ij.1*α ij.1 ij.2) ∧
      (∀ ij,M.paths ij=Fin.snoc (L.paths ij.1) (ij.2:ℂ)) ∧
      M.endpointVariance=_root_.DerivativeChainPhaseLock.parentVariance a L α ∧
      M.meanSquareCost ≤ K*M.endpointVariance ∧ _root_.DerivativeChainPrefixLaws.bellmanValue a K ≤ 0 := by
  obtain ⟨M,hw,hz,hvar,henergy,hrms⟩ :=
    _root_.DerivativeChainPhaseLock.actual_barycentric_extension a b u hderiv L α hα hαsum hαmean
  have he0 := _root_.DerivativeChainPhaseLock.edge_energy_nonneg a L α hα
  have hvd : L.endpointVariance ≤ M.endpointVariance := by linarith only [he0,henergy]
  have hg : M.endpointVariance=0 ∨
      Real.sqrt (L.endpointVariance/M.endpointVariance) ≤ (K-1)/(K+1) := by
    simpa only [hvar] using hgain
  have hbudget : M.meanSquareCost ≤ K*M.endpointVariance :=
    _root_.DerivativeChainPhaseLock.large_gain_rms_budget K L.meanSquareCost L.endpointVariance M.endpointVariance
      M.meanSquareCost hK L.endpointVariance_nonneg hvd M.meanSquareCost_nonneg hchild hrms hg
  exact ⟨M,hw,hz,hvar,hbudget,_root_.DerivativeChainPrefixLaws.bellmanValue_nonpos_of_history_law M K hbudget⟩
