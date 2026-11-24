-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.surjective_of_isPullback_blowupMorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:18.136257+00:00
-- url     : https://prove2.me/submissions/3bb485bc-6213-40d1-b853-0b431821b148

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_projectionToBase_of_isPullback_blowupMorphism

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X' X : Scheme.{u}} (g : X' ⟶ X)
    [AlgebraicGeometry.Surjective g]
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ i : ℕ, ∀ hi : i ≤ L, AlgebraicGeometry.Surjective (σ i hi) := by
  intro i hi
  have hsq : IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s L σ hzero hstep i hi
  have hg : AlgebraicGeometry.Surjective g := inferInstance
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hsq.flip hg
end FunctorialResolution.EmbeddedResolution
