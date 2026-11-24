-- Prove2me | solution 1 for DimdPolyLEAN.realHermite1D_memLp_inner_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:34.46462+00:00
-- url     : https://prove2.me/submissions/6b8ac2a4-9825-4b0b-ada5-04cdb05d3e56

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_no_conj_interchange_of_finite_sum
public import Theorems.Thm_DimdPolyLEAN_realHermite1D_memLp
public import Theorems.Thm_DimdPolyLEAN_realHermite1D_memLp_inner_orthonormal_of_no_conj_interchange

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution :
    (∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ)) ∧
      ∀ n m : Nat,
        (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
          if n = m then (1 : ℂ) else 0 := by
  /-
  Remaining one-dimensional analytic core.  The generating-function identity
  `realHermiteGenerating_integral_mul_conj` and the derivative coefficient
  lemma above reduce the Gram identity to differentiating under the integral.
  `MemLp` follows from the corresponding polynomial-times-Gaussian expression.
  -/
  refine realHermite1D_memLp_inner_orthonormal_of_no_conj_interchange ?_ ?_
  · intro n
    exact realHermite1D_memLp n
  · intro n m
    exact realHermiteGenerating_no_conj_interchange_of_finite_sum n m
end DimdPolyLEAN
