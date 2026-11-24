-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:18.3666+00:00
-- url     : https://prove2.me/submissions/5cb61c45-8e4c-4a5e-96ab-bd244a698c08

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_add
public import Theorems.Thm_DimdPolyLEAN_realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff_of_even_add
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
    (n k : ℕ) :
    realHermiteGeneratingExpansionCoeff n k =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((Real.sqrt 2 : ℂ) ^ k * ((Polynomial.hermite n).coeff k : ℂ))) := by
  by_cases hk : k ≤ n
  · by_cases heven : Even (n + k)
    · exact realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff_of_even_add hk heven
    · have hodd : Odd (n + k) := Nat.not_even_iff_odd.mp heven
      rw [realHermiteGeneratingExpansionCoeff_eq_zero_of_odd_add hk hodd,
        Polynomial.coeff_hermite_of_odd_add hodd]
      ring
  · have hlt : n < k := Nat.lt_of_not_ge hk
    rw [Polynomial.coeff_hermite_of_lt hlt]
    simp [realHermiteGeneratingExpansionCoeff, Nat.choose_eq_zero_of_lt hlt]
end DimdPolyLEAN
