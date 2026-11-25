-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.rootBranch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:58:13.836323+00:00
-- url     : https://prove2.me/submissions/a6357e38-ef67-4ae1-a4ce-8bf1a9986b7a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_detC
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_image_A
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_injOn_A
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_measurableSet_A


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (F : ℂ → E)
    (hF : Integrable (fun z => ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z)) :
    Integrable (fun c => F (NthRootMeasurability.R s k (u * c))) ∧
      ∫ c, F (NthRootMeasurability.R s k (u * c)) = ∫ z in NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
  have hA : MeasurableSet (NthRootMeasurability.A s k) := Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A s k

  have hderiv : ∀ z ∈ NthRootMeasurability.A s k, HasFDerivWithinAt (fun z => u⁻¹ * z ^ s)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ)
      (NthRootMeasurability.A s k) z := fun z _ =>
    (((hasDerivAt_pow s z).const_mul u⁻¹).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj := Formalism.FourierDecayAlt.P.NthRootMeasurability.injOn_A s k u hu
  have himg := Formalism.FourierDecayAlt.P.NthRootMeasurability.image_A s k hs u hu
  have hdet : ∀ z : ℂ, |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ).det| = ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 := fun z => by
    rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.detC, abs_of_nonneg (by positivity)]
  have hback : ∀ z ∈ NthRootMeasurability.A s k, F (NthRootMeasurability.R s k (u * (u⁻¹ * z ^ s))) = F z := fun z hz => by
    rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul, hz.2]
  have hnull : (volume : Measure ℂ).restrict ({0}ᶜ : Set ℂ) = volume := MeasureTheory.restrict_compl_singleton 0
  constructor
  · have h1 : IntegrableOn (fun c => F (NthRootMeasurability.R s k (u * c))) ((fun z => u⁻¹ * z ^ s) '' NthRootMeasurability.A s k) := by
      rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hA hderiv hinj]
      refine (hF.integrableOn (s := NthRootMeasurability.A s k)).congr_fun (fun z hz => ?_) hA
      simp only [hdet, hback z hz]
    rw [himg, IntegrableOn, hnull] at h1
    exact h1
  · have h2 := integral_image_eq_integral_abs_det_fderiv_smul volume hA hderiv hinj
      (fun c => F (NthRootMeasurability.R s k (u * c)))
    rw [himg, hnull] at h2
    rw [h2]
    refine setIntegral_congr_fun hA (fun z hz => ?_)
    simp only [hdet, hback z hz]
end Formalism.FourierDecayAlt.P.PBK
