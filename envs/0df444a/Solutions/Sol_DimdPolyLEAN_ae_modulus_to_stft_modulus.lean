-- Prove2me | solution 1 for DimdPolyLEAN.ae_modulus_to_stft_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:31.560883+00:00
-- url     : https://prove2.me/submissions/3f270068-d93d-4344-942d-5390a4167b36

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
public import Theorems.Thm_DimdPolyLEAN_stft_model_modulus
public import Theorems.Thm_DimdPolyLEAN_ae_modulus_to_pointwise_modulus

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
    ∀ ξ, ‖stftRep (varphiKappa kappa) (bKappa kappa U) ξ‖ =
      ‖stftRep (varphiKappa kappa) (bKappa kappa V) ξ‖ := by
  have hpoint := ae_modulus_to_pointwise_modulus hd kappa hmod
  intro ξ
  rw [stft_model_modulus hd kappa U ξ, stft_model_modulus hd kappa V ξ,
    hpoint (TKappa ξ)]
end DimdPolyLEAN
