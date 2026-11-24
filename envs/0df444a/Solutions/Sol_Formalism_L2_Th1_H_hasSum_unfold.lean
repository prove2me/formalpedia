-- Prove2me | solution 1 for Formalism.L2.Th1.H.hasSum_unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:24.646812+00:00
-- url     : https://prove2.me/submissions/6deba5a0-289d-4e3f-a3b6-25d14d9f0b05

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyGaussianIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnfoldingIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open scoped Pointwise
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {V E : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure V) [μ.IsAddLeftInvariant]
    (G : AddSubgroup V) [Countable G] {D : Set V} (hD : IsAddFundamentalDomain G D μ) {f : V → E}
    (hf : Integrable f μ) :
    HasSum (fun y : G => ∫ z in D, f (z - (y : V)) ∂μ) (∫ z, f z ∂μ) := by
  have h1 : HasSum (fun g : G => ∫ x in g +ᵥ D, f x ∂μ) (∫ z, f z ∂μ) := by
    have h := hasSum_integral_measure (μ := fun g : G => μ.restrict (g +ᵥ D)) (f := f)
      (by rwa [hD.sum_restrict])
    rwa [hD.sum_restrict] at h
  have h2 : ∀ g : G, ∫ x in g +ᵥ D, f x ∂μ = ∫ x in D, f (x - ((-g : G) : V)) ∂μ := by
    intro g
    rw [← Set.image_vadd,
      (measurePreserving_vadd g μ).setIntegral_image_emb (measurableEmbedding_const_vadd g) f D]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [AddSubgroup.vadd_def, add_comm]
  simp_rw [h2] at h1
  exact (Equiv.neg G).hasSum_iff.mp h1
end Formalism.L2.Th1.H
