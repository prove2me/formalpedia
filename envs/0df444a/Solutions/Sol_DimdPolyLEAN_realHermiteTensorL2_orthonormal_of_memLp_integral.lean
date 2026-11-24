-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteTensorL2_orthonormal_of_memLp_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:14.257635+00:00
-- url     : https://prove2.me/submissions/8a164590-bcac-4af9-9f63-e0811eb03b55

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteTensorL2_inner_eq_integral_of_memLp

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat}
    (hmem : ∀ alpha : Idx d,
      MemLp (realHermiteTensorRep alpha) 2
        (volume : Measure (RealVec d)))
    (hinner : ∀ alpha beta : Idx d,
      (∫ x : RealVec d,
        realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x)) =
        if alpha = beta then (1 : ℂ) else 0) :
    Orthonormal ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha) := by
  classical
  rw [orthonormal_iff_ite]
  intro alpha beta
  rw [realHermiteTensorL2_inner_eq_integral_of_memLp alpha beta
    (hmem alpha) (hmem beta)]
  exact hinner alpha beta
end DimdPolyLEAN
