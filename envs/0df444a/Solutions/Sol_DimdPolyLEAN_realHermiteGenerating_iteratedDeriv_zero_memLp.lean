-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_zero_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:14.575683+00:00
-- url     : https://prove2.me/submissions/13cc6942-5c6a-427d-9b9c-4a934ebee80c

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
public import Theorems.Thm_DimdPolyLEAN_complex_monomial_gaussian_memLp
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_iteratedDeriv_zero_expansion
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
theorem _root_.solution
    (n : ℕ) :
    MemLp (fun t : ℝ => iteratedDeriv n (realHermiteGenerating t) 0)
      2 (volume : Measure ℝ) := by
  have hsum :
      MemLp
        (fun t : ℝ =>
          ∑ k ∈ Finset.range (n + 1),
            ((((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
                ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
                  iteratedDeriv (n - k)
                    (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0)) *
              ((t : ℂ) ^ k * Complex.exp (-(((t : ℂ) ^ 2) / 2)))))
        2 (volume : Measure ℝ) := by
    refine MeasureTheory.memLp_finsetSum (Finset.range (n + 1)) ?_
    intro k hk
    exact (complex_monomial_gaussian_memLp k).const_mul
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
          iteratedDeriv (n - k)
            (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0))
  simpa [realHermiteGenerating_iteratedDeriv_zero_expansion] using hsum
end DimdPolyLEAN
