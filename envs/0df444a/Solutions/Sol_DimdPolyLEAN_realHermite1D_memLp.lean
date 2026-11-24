-- Prove2me | solution 1 for DimdPolyLEAN.realHermite1D_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:12.334367+00:00
-- url     : https://prove2.me/submissions/1a7f5e10-7851-4114-a20a-688600330fed

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_memLp

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution (n : ℕ) :
    MemLp (realHermite1D n) 2 (volume : Measure ℝ) := by
  refine MeasureTheory.MemLp.ae_eq ?_
    ((realHermiteGenerating_iteratedDeriv_zero_memLp n).const_mul
      ((Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)))
  filter_upwards with t
  rfl
end DimdPolyLEAN
