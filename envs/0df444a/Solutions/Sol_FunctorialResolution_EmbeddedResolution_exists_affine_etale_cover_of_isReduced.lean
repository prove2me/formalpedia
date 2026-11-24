-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_affine_etale_cover_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:39.948073+00:00
-- url     : https://prove2.me/submissions/7b5d88b5-9764-41cd-8a89-1b3f21851ee9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isAffine_sigmaOpens
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_surjective_sigmaOpensDesc
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_finite_affine_cover
import Theorems.Thm_AlgebraicGeometry_quasiCompact_of_compactSpace_of_subsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
universe u
private theorem subsingleton_spec_of_field (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced Y] :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (g : W ⟶ Y),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType q ∧ QuasiCompact q ∧
        Etale g ∧ Surjective g ∧ g ≫ p = q := by
  have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := subsingleton_spec_of_field k
  have hcs : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have hcY : CompactSpace ↥Y := by
    constructor
    have h := (‹QuasiCompact p›).isCompact_preimage Set.univ isOpen_univ isCompact_univ
    rwa [Set.preimage_univ] at h
  obtain ⟨ι, hι, U, hUaff, hUsup⟩ := exists_finite_affine_cover Y
  have : Finite ι := hι
  have hW : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  refine ⟨sigmaOpens Y U, sigmaOpensDesc Y U ≫ p, sigmaOpensDesc Y U, hW,
    isReduced_sigmaOpens Y U, ?_, ?_, etale_sigmaOpensDesc Y U,
    surjective_sigmaOpensDesc Y U hUsup, rfl⟩
  · infer_instance
  · exact quasiCompact_of_compactSpace_of_subsingleton _
end FunctorialResolution.EmbeddedResolution
