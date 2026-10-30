-- Prove2me | solution 1 for DerivativeChainPrefixLaws.uniform_step_centroid
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:34:57.592917+00:00
-- url     : https://prove2.me/submissions/d5db17a6-b687-4e37-af07-3475db8ad23b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
open DerivativeChainPrefixLaws


theorem solution (r : _root_.DerivativeChainContinuation.ComplexRootRows) (k : ℕ)
    (hstep : _root_.DerivativeChainContinuation.UniformPolynomialStep r k) :
    _root_.DerivativeChainContinuation.complexCentroid (r (k+1))=_root_.DerivativeChainContinuation.complexCentroid (r k) := by
  obtain ⟨_,K,hK,hKs,hKm,hKcol⟩ := hstep
  have hcol (i : Fin (k+2)) :
      (∑ j : Fin (k+1), (k+1:ℂ)⁻¹*(K j i:ℂ))=(k+2:ℂ)⁻¹ := by
    have hc := congrArg (Complex.ofReal : ℝ → ℂ) (hKcol i)
    simpa using hc
  have hm : (∑ j : Fin (k+1), (k+1:ℂ)⁻¹*r k j)=
      ∑ i : Fin (k+2), (k+2:ℂ)⁻¹*r (k+1) i := by
    calc
      _ = ∑ j : Fin (k+1), (k+1:ℂ)⁻¹*(∑ i, (K j i:ℂ)*r (k+1) i) := by
        simp only [hKm]
      _ = ∑ i : Fin (k+2), (∑ j : Fin (k+1), (k+1:ℂ)⁻¹*(K j i:ℂ))*r (k+1) i := by
        simp only [Finset.mul_sum,← mul_assoc]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = _ := by simp only [hcol]
  have hm' : (k+1:ℂ)⁻¹*(∑ j : Fin (k+1), r k j)=
      (k+2:ℂ)⁻¹*(∑ i : Fin (k+2), r (k+1) i) := by
    simpa only [Finset.mul_sum] using hm
  unfold _root_.DerivativeChainContinuation.complexCentroid
  push_cast
  convert hm'.symm using 1 <;> ring
