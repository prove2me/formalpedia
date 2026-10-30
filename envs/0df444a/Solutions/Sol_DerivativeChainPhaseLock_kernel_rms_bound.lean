-- Prove2me | solution 1 for DerivativeChainPhaseLock.kernel_rms_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:48:46.2583+00:00
-- url     : https://prove2.me/submissions/4b062c6c-50b8-49a4-8d6d-64dd345a0e5b

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPhaseLock_kernel_edge_energy
import Theorems.Thm_DerivativeChainPhaseLock_weighted_minkowski
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


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
universe v
namespace DerivativeChainPhaseLock
noncomputable section



theorem kernel_origin_expectation {n : ℕ} (a : Fin (n+2) → ℂ)
    {b : Fin (n+1) → ℂ} {u : ℂ} {κ : Type v} [Fintype κ]
    (L : FiniteBalancedHistoryLaw b u κ) (α : κ → (fromRoots a).roots.toFinset → ℝ)
    (hαsum : ∀ i, ∑ j, α i j=1) (f : κ → ℝ) :
    (∑ ij : κ × (fromRoots a).roots.toFinset, L.weights ij.1*α ij.1 ij.2*f ij.1)=
      ∑ i, L.weights i*f i := by
  simp only [Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum,← Finset.sum_mul,
    hαsum,one_mul]









end
end DerivativeChainPhaseLock


end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
universe v
open DerivativeChainPhaseLock










theorem solution {n : ℕ} (a : Fin (n+2) → ℂ)
    {b : Fin (n+1) → ℂ} {u : ℂ} {κ : Type v} [Fintype κ]
    (L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw b u κ) (α : κ → (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → ℝ)
    (hα : ∀ i j, 0 ≤ α i j) (hαsum : ∀ i, ∑ j, α i j=1)
    (hαmean : ∀ i, ∑ j, (α i j:ℂ)*(j:ℂ)=L.paths i (Fin.last n)) :
    Real.sqrt (_root_.DerivativeChainPhaseLock.parentSquareCost a L α) ≤ Real.sqrt L.meanSquareCost+
      Real.sqrt (_root_.DerivativeChainPhaseLock.parentVariance a L α-L.endpointVariance) := by
  let W : κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → ℝ := fun ij => L.weights ij.1*α ij.1 ij.2
  let A : κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → ℝ := fun ij => _root_.DerivativeChainPrivate.chainCost (L.paths ij.1)
  let B : κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → ℝ := fun ij =>
    ‖(ij.2:ℂ)-L.paths ij.1 (Fin.last n)‖
  have hW (ij) : 0 ≤ W ij := mul_nonneg (L.nonneg ij.1) (hα ij.1 ij.2)
  have hA : (∑ ij,W ij*(A ij)^2)=L.meanSquareCost := by
    simpa only [W,A,_root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.meanSquareCost] using
      _root_.DerivativeChainPhaseLock.kernel_origin_expectation a L α hαsum (fun i => _root_.DerivativeChainPrivate.chainCost (L.paths i)^2)
  have hB : (∑ ij,W ij*(B ij)^2)=_root_.DerivativeChainPhaseLock.parentVariance a L α-L.endpointVariance := by
    exact _root_.DerivativeChainPhaseLock.kernel_edge_energy a L α hαsum hαmean
  have hcost : (∑ ij,W ij*(A ij+B ij)^2)=_root_.DerivativeChainPhaseLock.parentSquareCost a L α := by
    simp only [_root_.DerivativeChainPhaseLock.parentSquareCost,W,A,B,_root_.DerivativeChainContinuation.complex_chainCost_snoc]
  have hrms := _root_.DerivativeChainPhaseLock.weighted_minkowski W A B hW
  rwa [hcost,hA,hB] at hrms
