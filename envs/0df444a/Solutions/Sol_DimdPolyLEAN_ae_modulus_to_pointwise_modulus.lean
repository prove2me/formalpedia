-- Prove2me | solution 1 for DimdPolyLEAN.ae_modulus_to_pointwise_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:04.714039+00:00
-- url     : https://prove2.me/submissions/a386ec24-7d8a-4643-bd47-e6f2a4133c8b

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
public import Theorems.Thm_DimdPolyLEAN_continuous_eq_of_ae_eq_gamma
public import Theorems.Thm_DimdPolyLEAN_continuous_toFun


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {U V : Skappa d kappa}
    (hmod :
      (fun z => ‖toFun kappa U z‖) =ᵐ[gammaD d]
        fun z => ‖toFun kappa V z‖) :
    ∀ z, ‖toFun kappa U z‖ = ‖toFun kappa V z‖ := by
  have hmodC :
      (fun z => ((‖toFun kappa U z‖ : ℝ) : ℂ)) =ᵐ[gammaD d]
        fun z => ((‖toFun kappa V z‖ : ℝ) : ℂ) := by
    filter_upwards [hmod] with z hz
    rw [hz]
  have hcontU : Continuous (fun z => ((‖toFun kappa U z‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_toFun hd kappa U).norm)
  have hcontV : Continuous (fun z => ((‖toFun kappa V z‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_toFun hd kappa V).norm)
  have hC := continuous_eq_of_ae_eq_gamma hd hcontU hcontV hmodC
  intro z
  exact Complex.ofReal_injective (congrFun hC z)
end DimdPolyLEAN
