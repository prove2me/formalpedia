-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:05.32916+00:00
-- url     : https://prove2.me/submissions/4305e959-b911-4d1b-9440-04b87d9f6f3f

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
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution (t : ℝ) (u : ℂ) :
    HasDerivAt (realHermiteGenerating t)
      (((Real.sqrt 2 : ℂ) * (t : ℂ) - u) * realHermiteGenerating t u) u := by
  have hpoly :
      HasDerivAt
        (fun v : ℂ =>
          -(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * v - v ^ 2 / 2)
        ((Real.sqrt 2 : ℂ) * (t : ℂ) - u) u := by
    have hlin :
        HasDerivAt (fun v : ℂ => (Real.sqrt 2 : ℂ) * (t : ℂ) * v)
          ((Real.sqrt 2 : ℂ) * (t : ℂ)) u := by
      simpa using HasDerivAt.const_mul
        ((Real.sqrt 2 : ℂ) * (t : ℂ)) (hasDerivAt_id u)
    have hquad : HasDerivAt (fun v : ℂ => v ^ 2 / 2) u u := by
      simpa [id, two_mul] using
        HasDerivAt.div_const ((hasDerivAt_id u).fun_pow 2) 2
    exact ((hlin.add_const (-(((t : ℂ) ^ 2) / 2))).sub hquad).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => by simp only [Pi.sub_apply]; ring)
  unfold realHermiteGenerating
  exact (HasDerivAt.const_mul
    (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) hpoly.cexp).congr_deriv (by ring)
end DimdPolyLEAN
