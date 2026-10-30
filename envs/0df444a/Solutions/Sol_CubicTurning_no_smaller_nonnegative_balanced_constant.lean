-- Prove2me | solution 1 for CubicTurning.no_smaller_nonnegative_balanced_constant
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:49:26.558281+00:00
-- url     : https://prove2.me/submissions/19bd6593-3986-48d1-a86d-9387136401a2

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_sharp_finite_balanced_law_lower
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning













































theorem variance_decomposition (r : ℝ) (a b c : ℂ)
    (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2) :
    variance a b c = 2*r^2+(2/3)*(a.im^2+b.im^2+c.im^2) := by
  have h := congrArg Complex.re hsecond
  simp [pow_two,Complex.mul_re] at h
  unfold variance
  rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  nlinarith
































































end CubicTurning


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning














theorem sharp_family_second (t : ℝ) :
    (sharpCentral t)^2+(sharpOuterPlus t)^2+(sharpOuterMinus t)^2=6 := by
  have hs : (Real.sqrt (3+3*t^2/4))^2=3+3*t^2/4 := Real.sq_sqrt (by positivity)
  simp only [pow_two] at hs
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus,pow_two,
    Complex.mul_re,Complex.mul_im] <;> nlinarith [hs]

theorem sharp_family_variance (t : ℝ) :
    variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)=2+t^2 := by
  have hv := variance_decomposition 1 (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)
    (by simpa using sharp_family_second t)
  convert hv using 1 <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus] <;> ring
















































end CubicTurning

open CubicTurning in
theorem solution (K : ℝ) (hK₀ : 0≤K) (hK : K<2/3) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧
      ∀ (n : ℕ) (L : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)),
        K*variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)<L.meanEnergy := by
  let t := Real.sqrt (2/3-K)
  have hδ : 0<2/3-K := sub_pos.mpr hK
  have ht : 0<t := Real.sqrt_pos.mpr hδ
  have hs : t^2=2/3-K := Real.sq_sqrt hδ.le
  have ht1 : t≤1 := by dsimp [t]; apply Real.sqrt_le_iff.mpr; constructor <;> linarith
  refine ⟨t,ht,ht1,?_⟩
  intro n L
  have hlo := sharp_finite_balanced_law_lower t ht ht1 L
  have hroot : 1≤Real.sqrt (1+t^2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])
  rw [sharp_family_variance]
  have hkgt : K*(2+t^2)<4/3 := by
    have hm : 0<(2/3-K)*(2-K) := mul_pos hδ (by linarith)
    nlinarith [hs]
  linarith
