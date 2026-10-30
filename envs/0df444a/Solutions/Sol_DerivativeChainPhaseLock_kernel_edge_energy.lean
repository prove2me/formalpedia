-- Prove2me | solution 1 for DerivativeChainPhaseLock.kernel_edge_energy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:46:41.726569+00:00
-- url     : https://prove2.me/submissions/b47df439-2145-44bc-ab3b-6fd4304c38ef

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
import Definitions.Def_DerivativeChainAnalytic_BarycentricMoments
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
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
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
universe v
open DerivativeChainPhaseLock






theorem solution {n : ℕ} (a : Fin (n+2) → ℂ)
    {b : Fin (n+1) → ℂ} {u : ℂ} {κ : Type v} [Fintype κ]
    (L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw b u κ) (α : κ → (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → ℝ)
    (hαsum : ∀ i, ∑ j, α i j=1)
    (hαmean : ∀ i, ∑ j, (α i j:ℂ)*(j:ℂ)=L.paths i (Fin.last n)) :
    _root_.DerivativeChainPhaseLock.edgeSquareEnergy a L α=_root_.DerivativeChainPhaseLock.parentVariance a L α-L.endpointVariance := by
  have hlocal (i : κ) :
      (∑ j, α i j*‖(j:ℂ)-u‖^2)=‖L.paths i (Fin.last n)-u‖^2+
        ∑ j, α i j*‖(j:ℂ)-L.paths i (Fin.last n)‖^2 :=
    _root_.DerivativeChainContinuation.finite_weighted_variance (α i) (fun j => (j:ℂ)) (L.paths i (Fin.last n)) u
      (hαsum i) (hαmean i)
  have heq : _root_.DerivativeChainPhaseLock.parentVariance a L α=L.endpointVariance+_root_.DerivativeChainPhaseLock.edgeSquareEnergy a L α := by
    calc
      _root_.DerivativeChainPhaseLock.parentVariance a L α = ∑ i, L.weights i*(∑ j,α i j*‖(j:ℂ)-u‖^2) := by
        simp only [_root_.DerivativeChainPhaseLock.parentVariance,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]
      _ = ∑ i, L.weights i*(‖L.paths i (Fin.last n)-u‖^2+
          ∑ j,α i j*‖(j:ℂ)-L.paths i (Fin.last n)‖^2) := by simp_rw [hlocal]
      _ = L.endpointVariance+_root_.DerivativeChainPhaseLock.edgeSquareEnergy a L α := by
        simp only [_root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.endpointVariance,_root_.DerivativeChainPhaseLock.edgeSquareEnergy,
          Fintype.sum_prod_type,mul_add,mul_assoc,← Finset.mul_sum,Finset.sum_add_distrib]
  linarith only [heq]
