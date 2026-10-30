-- Prove2me | solution 1 for DerivativeChainContinuation.sharp_cubic_endpoint_attained
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:51:42.407985+00:00
-- url     : https://prove2.me/submissions/cb3894ea-d86f-4e01-8a9a-318f7b67691e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainContinuation_SharpCubicTriangle
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


set_option autoImplicit false
namespace DerivativeChainContinuation



theorem sharpCubicConstant_positive : 0 < sharpCubicConstant := by
  unfold sharpCubicConstant
  positivity

theorem sharpCubicConstant_equation :
    3*sharpCubicConstant^2-2*sharpCubicConstant-3=0 := by
  unfold sharpCubicConstant
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  nlinarith



theorem sharpCubicConstant_sq_lt_three : sharpCubicConstant^2 < 3 := by
  have he := sharpCubicConstant_equation
  have hp := sharpCubicConstant_positive
  have hb : sharpCubicConstant < 3/2 := by
    unfold sharpCubicConstant
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
    have hn := Real.sqrt_nonneg 10
    nlinarith
  nlinarith



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution :
    ∃ (A R : ℝ) (B a o : ℂ), 0 ≤ A ∧ 0 < R ∧ 0 ≤ B.re ∧ 0 ≤ B.im ∧
      0 ≤ a.re ∧ 0 ≤ a.im ∧ a^3-(A:ℂ)*a-B=0 ∧
      (∀ z : ℂ, z^3-(A:ℂ)*z-B=0 → ‖z-o‖ ≤ R) ∧
      a.re+a.im=sharpCubicConstant*R := by
  let t := sharpCubicConstant
  have ht : 0 < t := sharpCubicConstant_positive
  have ht0 : t ≠ 0 := ne_of_gt ht
  let A := 1-t^2/3
  let B : ℂ := ⟨0,2*t*(9+t^2)/27⟩
  let a := cubicTriangleA 1 t
  let b := cubicTriangleB 1 t
  let c := cubicTriangleC 1 t
  let o : ℂ := ⟨0,(3-t^2)/(6*t)⟩
  let R := (1+t^2)/(2*t)
  have hR : 0 < R := by dsimp [R]; positivity
  have hpoly (z : ℂ) : z^3-(A:ℂ)*z-B = (z-a)*(z-b)*(z-c) := by
    apply Complex.ext <;>
      simp [A,B,a,b,c,cubicTriangleA,cubicTriangleB,cubicTriangleC,pow_succ,
        Complex.mul_re,Complex.mul_im] <;> ring
  have ha : a^3-(A:ℂ)*a-B=0 := by rw [hpoly]; simp
  have hnorma : Complex.normSq (a-o)=R^2 := by
    simp [a,o,R,cubicTriangleA,Complex.normSq_apply]
    field_simp
    ring
  have hnormb : Complex.normSq (b-o)=R^2 := by
    simp [b,o,R,cubicTriangleB,Complex.normSq_apply]
    field_simp
    ring
  have hnormc : Complex.normSq (c-o)=R^2 := by
    simp [c,o,R,cubicTriangleC,Complex.normSq_apply]
    field_simp
    ring
  have hnorm (z : ℂ) (hz : Complex.normSq (z-o)=R^2) : ‖z-o‖ ≤ R := by
    rw [Complex.normSq_eq_norm_sq] at hz
    exact (sq_le_sq₀ (norm_nonneg _) hR.le).mp hz.le
  refine ⟨A,R,B,a,o,?_,hR,?_,?_,?_,?_,ha,?_,?_⟩
  · dsimp [A]; have h := sharpCubicConstant_sq_lt_three; dsimp [t]; linarith
  · simp [B]
  · dsimp [B]; positivity
  · simp [a,cubicTriangleA]
  · dsimp [a,cubicTriangleA]; positivity
  · intro z hz
    rw [hpoly] at hz
    have hh : z=a ∨ z=b ∨ z=c := by
      simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using hz
    rcases hh with rfl|rfl|rfl
    · exact hnorm _ hnorma
    · exact hnorm _ hnormb
    · exact hnorm _ hnormc
  · have he := sharpCubicConstant_equation
    change 1+1*t/3 = t*((1+t^2)/(2*t))
    field_simp
    dsimp [t]
    nlinarith
