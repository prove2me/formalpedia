-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_integral_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:01.962545+00:00
-- url     : https://prove2.me/submissions/2321b465-c55c-4fdc-abfc-988b3bc90762

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_integral_mul

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution (u w : ℂ) :
    (∫ t : ℝ, realHermiteGenerating t u * star (realHermiteGenerating t w)) =
      Complex.exp (u * star w) := by
  simp_rw [realHermiteGenerating_conj]
  exact realHermiteGenerating_integral_mul u (star w)
end DimdPolyLEAN
