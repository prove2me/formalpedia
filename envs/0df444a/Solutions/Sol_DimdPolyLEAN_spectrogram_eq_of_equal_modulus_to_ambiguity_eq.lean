-- Prove2me | solution 1 for DimdPolyLEAN.spectrogram_eq_of_equal_modulus_to_ambiguity_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:37.741108+00:00
-- url     : https://prove2.me/submissions/6e7f1490-70de-4133-8763-95e89097f753

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
public import Theorems.Thm_DimdPolyLEAN_windowAmbiguity_dense_nonvanishing
public import Theorems.Thm_DimdPolyLEAN_continuous_ambiguityRep
public import Theorems.Thm_DimdPolyLEAN_spectrogram_ambiguity_identity
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    {f g : L2Real d}
    (hmod : ∀ ξ : PhaseSpace d,
      ‖stftRep (varphiKappa kappa) f ξ‖ =
        ‖stftRep (varphiKappa kappa) g ξ‖) :
    ∀ ξ : PhaseSpace d, ambiguityRep f f ξ = ambiguityRep g g ξ := by
  let hwin := varphiKappa kappa
  let s : Set (PhaseSpace d) :=
    {ξ | ambiguityRep hwin hwin ξ ≠ 0}
  have h_on : Set.EqOn (ambiguityRep f f) (ambiguityRep g g) s := by
    intro ξ hξ
    have hspec_eq :
        symplecticFourierRep
            (fun η : PhaseSpace d => ((‖stftRep hwin f η‖ ^ 2 : ℝ) : ℂ)) ξ =
          symplecticFourierRep
            (fun η : PhaseSpace d => ((‖stftRep hwin g η‖ ^ 2 : ℝ) : ℂ)) ξ := by
      congr 1
      funext η
      rw [hmod η]
    have hf_id := spectrogram_ambiguity_identity hwin f ξ
    have hg_id := spectrogram_ambiguity_identity hwin g ξ
    have hprod :
        ambiguityRep f f ξ * star (ambiguityRep hwin hwin ξ) =
          ambiguityRep g g ξ * star (ambiguityRep hwin hwin ξ) := by
      simp_all only [Prod.forall, Complex.ofReal_pow, RCLike.star_def, mul_eq_mul_right_iff,
        map_eq_zero]
    exact mul_right_cancel₀ (star_ne_zero.mpr hξ) hprod
  have hs_dense : Dense s := by exact windowAmbiguity_dense_nonvanishing hd kappa
  have hamb : ambiguityRep f f = ambiguityRep g g :=
    Continuous.ext_on hs_dense (continuous_ambiguityRep f f)
      (continuous_ambiguityRep g g) h_on
  simp_all only [Prod.forall, implies_true]
end DimdPolyLEAN
