-- Prove2me | solution 1 for DerivativeChainPhaseLock.birkhoff_cost_selection
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:17:04.404634+00:00
-- url     : https://prove2.me/submissions/0f3d892a-887a-4281-ab98-a82272eec6c1

import Mathlib
import Theorems.Thm_DerivativeChainPrivate_exists_nonpos_of_probability_mean_zero
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
open Matrix
universe v
open DerivativeChainPhaseLock

theorem solution {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S ∈ doublyStochastic ℝ ι) (c : ι → ι → ℝ) :
    ∃ σ : Equiv.Perm ι, (∑ i,c i (σ i)) ≤ ∑ i,∑ j,S i j*c i j := by
  obtain ⟨w,hw,hws,hrepr⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hentry (i j : ι) : (∑ σ,w σ*σ.permMatrix ℝ i j)=S i j := by
    have h := congrArg (fun A : Matrix ι ι ℝ => A i j) hrepr
    simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using h
  have hpc (σ : Equiv.Perm ι) (i : ι) : ∑ j,σ.permMatrix ℝ i j*c i j=c i (σ i) := by
    have h := congrArg (fun f : ι → ℝ => f i)
      (Matrix.permMatrix_mulVec (σ:=σ) (v:=fun j => c i j))
    simpa only [Matrix.mulVec,dotProduct,Function.comp_apply] using h
  have hmean : (∑ σ,w σ*(∑ i,c i (σ i)))=∑ i,∑ j,S i j*c i j := by
    symm
    calc
      (∑ i,∑ j,S i j*c i j) = ∑ i,∑ j,(∑ σ,w σ*σ.permMatrix ℝ i j)*c i j := by
        simp_rw [hentry]
      _ = ∑ i,∑ σ,∑ j,w σ*σ.permMatrix ℝ i j*c i j := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ σ,∑ i,∑ j,w σ*σ.permMatrix ℝ i j*c i j := Finset.sum_comm
      _ = ∑ σ,w σ*(∑ i,c i (σ i)) := by
        simp only [mul_assoc,← Finset.mul_sum,hpc]
  let f : Equiv.Perm ι → ℝ := fun σ => ∑ i,c i (σ i)
  have hzero : (∑ σ,w σ*(f σ-∑ τ,w τ*f τ))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hws,one_mul,sub_self]
  obtain ⟨σ,hσ⟩ := _root_.DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero w _ hw hws hzero
  have hle : f σ ≤ ∑ τ,w τ*f τ := sub_nonpos.mp hσ
  dsimp only [f] at hle
  exact ⟨σ,by rwa [hmean] at hle⟩
