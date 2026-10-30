-- Prove2me | solution 1 for DerivativeChainPhaseLock.actual_kernel_extension
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:46:21.354843+00:00
-- url     : https://prove2.me/submissions/223ddd33-aec7-457d-a31a-bd1a61c27f84

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainPrivate_foundations
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













theorem rootProbability_support {P : ℂ[X]} (hP : 0 < P.degree)
    (w : P.roots.toFinset) : P.eval (w : ℂ) = 0 := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  exact (Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp w.property)





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





theorem prefix_root_lift {n : ℕ} (a : Fin (n+2) → ℂ) (b : Fin (n+1) → ℂ)
    (hderiv : (fromRoots a).derivative=C (n+2:ℂ)*fromRoots b)
    (z : Fin (n+1) → ℂ) (hz : IsChain b z) (k : Fin (n+1)) :
    (row a (k.val+1)).eval (z k)=0 := by
  have hh := hz k
  simp only [row] at hh ⊢
  rw [show n+2-(k.val+1)=(n+1-(k.val+1))+1 by omega,
    Function.iterate_succ_apply,hderiv,iterate_derivative_C_mul,eval_mul,eval_C,hh,mul_zero]



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








theorem solution {n : ℕ} (a : Fin (n+2) → ℂ) (b : Fin (n+1) → ℂ) (u : ℂ)
    {κ : Type v} [Fintype κ]
    (hderiv : (_root_.DerivativeChainPrivate.fromRoots a).derivative=C (n+2:ℂ)*_root_.DerivativeChainPrivate.fromRoots b)
    (L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw b u κ)
    (α : κ → (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → ℝ)
    (hα : ∀ i j, 0 ≤ α i j) (hαsum : ∀ i, ∑ j, α i j=1)
    (hαmean : ∀ i, ∑ j, (α i j:ℂ)*(j:ℂ)=L.paths i (Fin.last n)) :
    ∃ M : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a u (κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset),
      (∀ ij, M.weights ij=L.weights ij.1*α ij.1 ij.2) ∧
      (∀ ij, M.paths ij=Fin.snoc (L.paths ij.1) (ij.2:ℂ)) ∧
      M.endpointVariance=_root_.DerivativeChainPhaseLock.parentVariance a L α ∧
      M.meanSquareCost=_root_.DerivativeChainPhaseLock.parentSquareCost a L α := by
  classical
  have hP : 0 < (_root_.DerivativeChainPrivate.fromRoots a).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    unfold _root_.DerivativeChainPrivate.fromRoots
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp
  let W : κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → ℝ := fun ij => L.weights ij.1*α ij.1 ij.2
  let Z : κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset → Fin (n+2) → ℂ := fun ij => Fin.snoc (L.paths ij.1) (ij.2:ℂ)
  have hWs : ∑ ij, W ij=1 := by
    simp only [W,Fintype.sum_prod_type,← Finset.mul_sum,hαsum,mul_one,L.total]
  have hWmean : ∑ ij, (W ij:ℂ)*Z ij (Fin.last (n+1))=u := by
    simp only [W,Z,Fintype.sum_prod_type,Fin.snoc_last,Complex.ofReal_mul,mul_assoc,
      ← Finset.mul_sum,hαmean,L.balanced]
  let M : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a u (κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset) := {
    weights := W
    nonneg := fun ij => mul_nonneg (L.nonneg ij.1) (hα ij.1 ij.2)
    total := hWs
    paths := Z
    actual := by
      intro ij k
      induction k using Fin.lastCases with
      | last =>
        simpa only [Z,Fin.snoc_last,Fin.val_last,_root_.DerivativeChainPrivate.row,
          show n+2-(n+1+1)=0 by omega,Function.iterate_zero_apply] using
          _root_.DerivativeChain.rootProbability_support hP ij.2
      | cast k =>
        simp only [Z,Fin.snoc_castSucc,Fin.val_castSucc]
        exact _root_.DerivativeChainPhaseLock.prefix_root_lift a b hderiv (L.paths ij.1) (L.actual ij.1) k
    start := by
      intro ij
      change Z ij (0:Fin (n+1)).castSucc=u
      simp only [Z,Fin.snoc_castSucc,L.start]
    balanced := hWmean }
  refine ⟨M,(fun _ => rfl),(fun _ => rfl),?_,rfl⟩
  change (∑ ij : κ × (_root_.DerivativeChainPrivate.fromRoots a).roots.toFinset, W ij*‖Z ij (Fin.last (n+1))-u‖^2)=_root_.DerivativeChainPhaseLock.parentVariance a L α
  simp only [_root_.DerivativeChainPhaseLock.parentVariance,W,Z,Fin.snoc_last]
