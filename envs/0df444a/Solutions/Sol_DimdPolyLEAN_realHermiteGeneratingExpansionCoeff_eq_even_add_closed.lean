-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_even_add_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:00.697384+00:00
-- url     : https://prove2.me/submissions/3ddef5e2-688e-4c96-8eb8-1e0b5e59e69d

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGeneratingExpansionCoeff_eq_of_even_sub

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {n k : ℕ} (hk : k ≤ n) (heven : Even (n + k)) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          ((-1 : ℂ) ^ ((n - k) / 2) *
            (((n - k) - 1)‼ : ℂ)))) := by
  apply realHermiteGeneratingExpansionCoeff_eq_of_even_sub
  rw [Nat.even_sub hk]
  exact Nat.even_add.mp heven
end DimdPolyLEAN
