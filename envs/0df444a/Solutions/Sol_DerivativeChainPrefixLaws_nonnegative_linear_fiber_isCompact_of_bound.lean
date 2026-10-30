-- Prove2me | solution 1 for DerivativeChainPrefixLaws.nonnegative_linear_fiber_isCompact_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:46:05.899622+00:00
-- url     : https://prove2.me/submissions/e116af5d-a5e8-44e6-862d-1203eee61dce

import Mathlib
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
open DerivativeChainPrefixLaws


theorem solution {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : (ι → ℝ) →ₗ[ℝ] F) (b : F) (B : ι → ℝ)
    (hbound : ∀ w : ι → ℝ,(∀ i,0 ≤ w i) → A w=b → ∀ i,w i ≤ B i) :
    IsCompact {w : ι → ℝ | (∀ i,0 ≤ w i) ∧ A w=b} := by
  have hclosed : IsClosed {w : ι → ℝ | (∀ i,0 ≤ w i) ∧ A w=b} := by
    have he : {w : ι → ℝ | (∀ i,0 ≤ w i) ∧ A w=b}=
        (⋂ i : ι,{w : ι → ℝ | 0 ≤ w i}) ∩ {w : ι → ℝ | A w=b} := by
      ext w
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
    rw [he]
    exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
      (isClosed_eq A.continuous_of_finiteDimensional continuous_const)
  have hsub : {w : ι → ℝ | (∀ i,0 ≤ w i) ∧ A w=b} ⊆
      Set.univ.pi (fun i : ι => Set.Icc (0:ℝ) (B i)) := by
    intro w hw
    exact Set.mem_univ_pi.mpr (fun i => ⟨hw.1 i,hbound w hw.1 hw.2 i⟩)
  exact (isCompact_univ_pi (fun i : ι => isCompact_Icc)).of_isClosed_subset hclosed hsub
