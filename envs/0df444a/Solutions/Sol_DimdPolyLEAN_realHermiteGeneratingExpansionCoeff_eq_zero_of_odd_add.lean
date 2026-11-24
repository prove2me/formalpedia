-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:55.798334+00:00
-- url     : https://prove2.me/submissions/d5da076e-ecf4-4f0d-a77a-87e13ef078b7

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {n k : ℕ} (hk : k ≤ n) (hodd : Odd (n + k)) :
    realHermiteGeneratingExpansionCoeff n k = 0 := by
  apply realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_sub
  rw [Nat.odd_sub hk]
  exact Nat.odd_add.mp hodd
end DimdPolyLEAN
