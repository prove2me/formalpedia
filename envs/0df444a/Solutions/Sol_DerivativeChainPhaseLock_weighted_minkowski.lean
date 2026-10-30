-- Prove2me | solution 1 for DerivativeChainPhaseLock.weighted_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:46:08.407872+00:00
-- url     : https://prove2.me/submissions/0ac4f9ad-95fe-4920-8979-011e0b59157d

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
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
universe v
open DerivativeChainPhaseLock








theorem solution {ι : Type v} [Fintype ι] (w A B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (∑ i,w i*(A i+B i)^2) ≤
      Real.sqrt (∑ i,w i*(A i)^2)+Real.sqrt (∑ i,w i*(B i)^2) := by
  let A2 : ℝ := ∑ i,w i*(A i)^2
  let B2 : ℝ := ∑ i,w i*(B i)^2
  let T : ℝ := ∑ i,w i*A i*B i
  have hA2 : 0 ≤ A2 := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hB2 : 0 ≤ B2 := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hprod (i : ι) : (Real.sqrt (w i)*A i)*(Real.sqrt (w i)*B i)=w i*A i*B i := by
    calc
      _ = (Real.sqrt (w i))^2*(A i*B i) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i)]; ring
  have hAsq (i : ι) : (Real.sqrt (w i)*A i)^2=w i*(A i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hBsq (i : ι) : (Real.sqrt (w i)*B i)^2=w i*(B i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hcs : T^2 ≤ A2*B2 := by
    simpa only [A2,B2,T,hprod,hAsq,hBsq] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => Real.sqrt (w i)*A i) (fun i => Real.sqrt (w i)*B i)
  have hT : T ≤ Real.sqrt A2*Real.sqrt B2 := by
    simpa only [Real.sqrt_mul hA2] using Real.le_sqrt_of_sq_le hcs
  have hexpand : (∑ i,w i*(A i+B i)^2)=A2+2*T+B2 := by
    dsimp only [A2,B2,T]
    calc
      _ = ∑ i,(w i*(A i)^2+2*(w i*A i*B i)+w i*(B i)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have hsquare : (∑ i,w i*(A i+B i)^2) ≤ (Real.sqrt A2+Real.sqrt B2)^2 := by
    rw [hexpand]
    nlinarith only [hT,Real.sq_sqrt hA2,Real.sq_sqrt hB2]
  exact (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hsquare
