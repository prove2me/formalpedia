-- Prove2me | solution 1 for DerivativeChainPhaseLock.root_probability_extension
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:50:49.466758+00:00
-- url     : https://prove2.me/submissions/a0176106-1c94-43fd-99ad-c81e8350bd97

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
import Definitions.Def_DerivativeChainAnalytic_BarycentricMoments
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_RootProbabilityExtension
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainPhaseLock_actual_kernel_extension
import Theorems.Thm_DerivativeChainPhaseLock_kernel_edge_energy
import Theorems.Thm_DerivativeChainPhaseLock_kernel_rms_bound
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




open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChain



theorem rootProbability_nonneg (P : ℂ[X]) (z : ℂ) (w : P.roots.toFinset) :
    0 ≤ rootProbability P z w := by
  exact div_nonneg (P.derivRootWeight_nonneg z w)
    (Finset.sum_nonneg fun v _ => P.derivRootWeight_nonneg z v)

theorem sum_rootProbability {P : ℂ[X]} (hP : 0 < P.degree) (z : ℂ) :
    ∑ w : P.roots.toFinset, rootProbability P z w = 1 := by
  classical
  simp only [rootProbability, ← Finset.sum_div, Finset.sum_coe_sort]
  exact div_self (Polynomial.sum_derivRootWeight_pos hP z).ne'

theorem rootProbability_mean {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∑ w : P.roots.toFinset, rootProbability P z w • (w : ℂ) = z := by
  classical
  simp only [rootProbability, div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
  rw [Finset.sum_coe_sort P.roots.toFinset
    (fun w : ℂ => P.derivRootWeight z w • w)]
  exact (Polynomial.eq_centerMass_of_eval_derivative_eq_zero hP hz).symm











end DerivativeChain



open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChainPrivate







end DerivativeChainPrivate




end
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
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory
universe v
namespace DerivativeChainPhaseLock
noncomputable section



theorem child_endpoint_critical {n : ℕ} (a : Fin (n+2) → ℂ) (b : Fin (n+1) → ℂ)
    (u : ℂ) {κ : Type v} [Fintype κ]
    (hderiv : (fromRoots a).derivative=C (n+2:ℂ)*fromRoots b)
    (L : FiniteBalancedHistoryLaw b u κ) (i : κ) :
    (fromRoots a).derivative.eval (L.paths i (Fin.last n))=0 := by
  have hbroot : (fromRoots b).eval (L.paths i (Fin.last n))=0 := by
    simpa only [row,Fin.val_last,Nat.sub_self,Function.iterate_zero_apply] using
      L.actual i (Fin.last n)
  rw [hderiv,eval_mul,eval_C,hbroot,mul_zero]



end
end DerivativeChainPhaseLock


end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory
universe v
open DerivativeChainPhaseLock






theorem solution {n : ℕ} (a : Fin (n+2) → ℂ) (b : Fin (n+1) → ℂ)
    (u : ℂ) {κ : Type v} [Fintype κ]
    (hderiv : (_root_.DerivativeChainPrivate.fromRoots a).derivative=C (n+2:ℂ)*_root_.DerivativeChainPrivate.fromRoots b)
    (L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw b u κ) :
    ∃ M : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a u (κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset),
      (∀ ij,M.weights ij=L.weights ij.1*_root_.DerivativeChainPhaseLock.rootKernel a L ij.1 ij.2) ∧
      (∀ ij,M.paths ij=Fin.snoc (L.paths ij.1) (ij.2:ℂ)) ∧
      M.endpointVariance=_root_.DerivativeChainPhaseLock.parentVariance a L (_root_.DerivativeChainPhaseLock.rootKernel a L) ∧
      _root_.DerivativeChainPhaseLock.edgeSquareEnergy a L (_root_.DerivativeChainPhaseLock.rootKernel a L)=M.endpointVariance-L.endpointVariance ∧
      Real.sqrt M.meanSquareCost ≤ Real.sqrt L.meanSquareCost+
        Real.sqrt (M.endpointVariance-L.endpointVariance) := by
  have hP : 0 < (_root_.DerivativeChainPrivate.fromRoots a).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    unfold _root_.DerivativeChainPrivate.fromRoots
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp
  have hnonneg (i) (j) : 0 ≤ _root_.DerivativeChainPhaseLock.rootKernel a L i j :=
    _root_.DerivativeChain.rootProbability_nonneg (_root_.DerivativeChainPrivate.fromRoots a) (L.paths i (Fin.last n)) j
  have hsum (i) : ∑ j, _root_.DerivativeChainPhaseLock.rootKernel a L i j=1 :=
    _root_.DerivativeChain.sum_rootProbability hP (L.paths i (Fin.last n))
  have hmean (i) : ∑ j, (_root_.DerivativeChainPhaseLock.rootKernel a L i j:ℂ)*(j:ℂ)=L.paths i (Fin.last n) := by
    simpa only [_root_.DerivativeChainPhaseLock.rootKernel,Complex.real_smul] using _root_.DerivativeChain.rootProbability_mean hP
      (_root_.DerivativeChainPhaseLock.child_endpoint_critical a b u hderiv L i)
  exact _root_.DerivativeChainPhaseLock.actual_barycentric_extension a b u hderiv L (_root_.DerivativeChainPhaseLock.rootKernel a L) hnonneg hsum hmean
