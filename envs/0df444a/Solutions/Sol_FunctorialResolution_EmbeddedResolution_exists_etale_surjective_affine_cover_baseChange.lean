-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_etale_surjective_affine_cover_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:36.114974+00:00
-- url     : https://prove2.me/submissions/3b5cc831-4bbe-4149-9c93-11008e941c39

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_FieldExtensionEtaleCover
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isAffine_baseChange_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isReduced_baseChange_sigmaOpensDesc
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_finite_affine_cover
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isAffine_sigmaOpens
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_surjective_sigmaOpensDesc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
noncomputable section
variable {k : Type u} [Field k] {X W : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (K : Type u) [Field K] [Algebra k K] [IsReduced (baseChange f K)] :
    ∃ (W : Scheme.{u}) (c : W ⟶ X) (g : baseChange (c ≫ f) K ⟶ baseChange f K),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType (c ≫ f) ∧ QuasiCompact (c ≫ f) ∧
        Etale c ∧ Surjective c ∧
        IsAffine (baseChange (c ≫ f) K) ∧ IsReduced (baseChange (c ≫ f) K) ∧
        LocallyOfFiniteType (baseChangeToSpec (c ≫ f) K) ∧
        QuasiCompact (baseChangeToSpec (c ≫ f) K) ∧
        Etale g ∧ Surjective g ∧
        g ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K ∧
        g ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c := by
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace (f := f)
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  have := hι
  have hWaff : IsAffine (sigmaOpens X U) := isAffine_sigmaOpens X U hUaff
  have hsurj : Surjective (sigmaOpensDesc X U) := surjective_sigmaOpensDesc X U hUtop
  have hqc : QuasiCompact (sigmaOpensDesc X U ≫ f) := inferInstance
  have hbcaff : IsAffine (baseChange (sigmaOpensDesc X U ≫ f) K) :=
    isAffine_baseChange_comp f (sigmaOpensDesc X U) K
  refine ⟨sigmaOpens X U, sigmaOpensDesc X U, baseChangeMap f (sigmaOpensDesc X U) K,
    hWaff, inferInstance, inferInstance, hqc, inferInstance, hsurj, hbcaff,
    isReduced_baseChange_sigmaOpensDesc f K U, ?_, ?_, inferInstance, inferInstance,
    baseChangeMap_comp_baseChangeToSpec f (sigmaOpensDesc X U) K,
    baseChangeMap_comp_baseChangeProjection f (sigmaOpensDesc X U) K⟩
  · exact morphismProperty_of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback (sigmaOpensDesc X U ≫ f) (specMapAlgebraMap k K)).flip inferInstance
  · exact morphismProperty_of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (sigmaOpensDesc X U ≫ f) (specMapAlgebraMap k K)).flip inferInstance
end FunctorialResolution.EmbeddedResolution
