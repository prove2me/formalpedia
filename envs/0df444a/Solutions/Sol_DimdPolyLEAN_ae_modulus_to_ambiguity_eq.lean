-- Prove2me | solution 1 for DimdPolyLEAN.ae_modulus_to_ambiguity_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:38.542076+00:00
-- url     : https://prove2.me/submissions/ec6768a9-24f4-4a8b-bfb5-9afad9f8c45f

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
public import Theorems.Thm_DimdPolyLEAN_spectrogram_eq_of_equal_modulus_to_ambiguity_eq
public import Theorems.Thm_DimdPolyLEAN_ae_modulus_to_stft_modulus

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
    ∀ ξ, ambiguityRep (bKappa kappa U) (bKappa kappa U) ξ =
      ambiguityRep (bKappa kappa V) (bKappa kappa V) ξ := by
  exact spectrogram_eq_of_equal_modulus_to_ambiguity_eq hd kappa
    (ae_modulus_to_stft_modulus hd kappa hmod)
end DimdPolyLEAN
