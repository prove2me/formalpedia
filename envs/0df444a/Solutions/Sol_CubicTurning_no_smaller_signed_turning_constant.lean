-- Prove2me | solution 1 for CubicTurning.no_smaller_signed_turning_constant
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:51:56.524909+00:00
-- url     : https://prove2.me/submissions/b2755600-9d66-42ed-88ae-5349600e9b98

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_energy_eq_halfAngleEnergy
import Theorems.Thm_CubicTurning_no_smaller_nonnegative_balanced_constant
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

























theorem no_smaller_balanced_constant (K : ℝ) (hK : K<2/3) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧
      ∀ (n : ℕ) (L : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)),
        K*variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)<L.meanEnergy := by
  by_cases hK₀ : 0≤K
  · exact no_smaller_nonnegative_balanced_constant K hK₀ hK
  · refine ⟨1,by norm_num,by norm_num,?_⟩
    intro n L
    have hlo := sharp_finite_balanced_law_lower 1 (by norm_num) (by norm_num) L
    have hKn : K<0 := lt_of_not_ge hK₀
    have hpos : 0<L.meanEnergy := lt_of_lt_of_le (by positivity) hlo
    have hk : K*(2+(1:ℝ)^2)<0 := mul_neg_of_neg_of_pos hKn (by norm_num)
    rw [sharp_family_variance]
    exact hk.trans hpos

theorem balanced_meanEnergy_eq_half_angle {n : ℕ} {a b c : ℂ}
    (L : FiniteBalancedForwardLaw n a b c) :
    L.meanEnergy=∑ i,L.weights i*halfAngleEnergy (L.axes i)
      (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1) := by
  unfold FiniteBalancedForwardLaw.meanEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [energy_eq_halfAngleEnergy _ _ _ (L.forward i)]




















end CubicTurning

open CubicTurning in
theorem solution (K : ℝ) (hK : K<2/3) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧
      ∀ (n : ℕ) (L : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)),
        K*variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)<
          ∑ i,L.weights i*halfAngleEnergy (L.axes i)
            (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1) := by
  obtain ⟨t,ht,ht1,hbound⟩ := no_smaller_balanced_constant K hK
  refine ⟨t,ht,ht1,?_⟩
  intro n L
  rw [←balanced_meanEnergy_eq_half_angle L]
  exact hbound n L
