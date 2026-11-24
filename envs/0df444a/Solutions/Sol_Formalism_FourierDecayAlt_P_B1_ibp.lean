-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.ibp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:35:32.353803+00:00
-- url     : https://prove2.me/submissions/291a1011-40dd-4d3c-a3d9-3c5360c92d5a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution : RegIBP := by
  intro h hh hc x
  set e : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) with he
  have hed : ∀ t, HasDerivAt e (Complex.I * x * e t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * ((x * t : ℝ) : ℂ)) (Complex.I * x) t := by
      have h2 : HasDerivAt (fun t : ℝ => ((x * t : ℝ) : ℂ)) ((x : ℝ) : ℂ) t := by
        have := ((hasDerivAt_id t).const_mul x).ofReal_comp
        simpa using this
      exact h2.const_mul _
    have := h1.cexp
    simpa [he, mul_comm, mul_left_comm, mul_assoc] using this
  have hec : Continuous e := by
    rw [he]; fun_prop
  have hd1 : ContDiff ℝ 1 (deriv h) := by
    have : ContDiff ℝ (1 + 1) h := by simpa [one_add_one_eq_two] using hh
    exact ((contDiff_succ_iff_deriv).1 this).2.2
  have hh0 : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hh1 : Differentiable ℝ (deriv h) := hd1.differentiable (by norm_num)
  have c0 : Continuous h := hh.continuous
  have c1 : Continuous (deriv h) := hd1.continuous
  have c2 : Continuous (deriv (deriv h)) := hd1.continuous_deriv (le_refl _)
  have k1 : HasCompactSupport (deriv h) := hc.deriv
  have k2 : HasCompactSupport (deriv (deriv h)) := k1.deriv
  have i2 : iteratedDeriv 2 h = deriv (deriv h) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have I0 : Integrable (fun t => e t * h t) := (hec.mul c0).integrable_of_hasCompactSupport hc.mul_left
  have I1 : Integrable (fun t => e t * deriv h t) := (hec.mul c1).integrable_of_hasCompactSupport k1.mul_left
  have I2 : Integrable (fun t => e t * deriv (deriv h) t) := (hec.mul c2).integrable_of_hasCompactSupport k2.mul_left
  have J0 : Integrable (fun t => (Complex.I * x * e t) * h t) := by
    simpa [mul_assoc] using I0.const_mul (Complex.I * x)
  have J1 : Integrable (fun t => (Complex.I * x * e t) * deriv h t) := by
    simpa [mul_assoc] using I1.const_mul (Complex.I * x)
  have s1 : (∫ t, e t * deriv (deriv h) t) = - ∫ t, (Complex.I * x * e t) * deriv h t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hed t) (fun t _ => (hh1 t).hasDerivAt) I2 J1 I1
  have s2 : (∫ t, e t * deriv h t) = - ∫ t, (Complex.I * x * e t) * h t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hed t) (fun t _ => (hh0 t).hasDerivAt) I1 J0 I0
  have m1 : (∫ t, (Complex.I * x * e t) * deriv h t) = Complex.I * x * ∫ t, e t * deriv h t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have m0 : (∫ t, (Complex.I * x * e t) * h t) = Complex.I * x * ∫ t, e t * h t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have l : (∫ t : ℝ, (h t - iteratedDeriv 2 h t) * e t) = (∫ t, e t * h t) - ∫ t, e t * deriv (deriv h) t := by
    rw [← integral_sub I0 I2, i2]; congr 1; funext t; ring
  have r : (∫ t : ℝ, h t * e t) = ∫ t, e t * h t := by congr 1; funext t; ring
  rw [l, r, s1, m1, s2, m0]
  push_cast
  linear_combination (-(x:ℂ)^2 * ∫ t, e t * h t) * Complex.I_mul_I
end Formalism.FourierDecayAlt.P.B1
