-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.rootsInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:51.405263+00:00
-- url     : https://prove2.me/submissions/6cef3fcb-e76f-4b40-90b3-9eb4a02f40e8

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : StatRootsInt := by
  unfold StatRootsInt
  intro O _ _ _ P t α hP
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  have hmon : (P.map (algebraMap O (FractionRing O))).Monic := by
    rw [hP]
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hPm : P.Monic := by
    first
    | exact Polynomial.monic_of_injective hinj hmon
    | (rw [Polynomial.Monic, ← hinj.eq_iff, map_one, ← Polynomial.leadingCoeff_map_of_injective hinj]
       exact hmon)
  have hint : ∀ i, ∃ b : O, algebraMap O (FractionRing O) b = α i := by
    intro i
    have hroot : Polynomial.eval₂ (algebraMap O (FractionRing O)) (α i) P = 0 := by
      rw [Polynomial.eval₂_eq_eval_map, hP, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    exact IsIntegrallyClosed.isIntegral_iff.1 ⟨P, hPm, hroot⟩
  choose β hβ using hint
  refine ⟨β, hβ, ?_⟩
  apply Polynomial.map_injective _ hinj
  rw [hP, Polynomial.map_prod]
  simp [hβ]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
