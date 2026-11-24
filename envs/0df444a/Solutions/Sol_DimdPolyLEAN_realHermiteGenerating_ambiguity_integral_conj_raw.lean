-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_ambiguity_integral_conj_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:50.358805+00:00
-- url     : https://prove2.me/submissions/4032b980-6483-45d9-b141-8e6b2ea46699

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_conj
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_ambiguity_integral_raw

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    (x ω : ℝ) (u v : ℂ) :
    (∫ t : ℝ,
      realHermiteGenerating (t + x / 2) u *
        star (realHermiteGenerating (t - x / 2) v) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))) =
      Complex.exp
        (-((x : ℂ) ^ 2) / 4 +
          (Real.sqrt 2 : ℂ) * (x : ℂ) * u / 2 -
          (Real.sqrt 2 : ℂ) * (x : ℂ) * star v / 2 -
          (u ^ 2 + (star v) ^ 2) / 2 +
          (((Real.sqrt 2 : ℂ) * (u + star v) -
              (2 * Real.pi : ℂ) * Complex.I * (ω : ℂ)) ^ 2) / 4) := by
  simp_rw [realHermiteGenerating_conj]
  exact realHermiteGenerating_ambiguity_integral_raw x ω u (star v)
end DimdPolyLEAN
