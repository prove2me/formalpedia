-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPullback_projectionToBase_of_isPullback_blowupMorphism
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:26.909516+00:00
-- url     : https://prove2.me/submissions/457d68e5-cdc7-4eed-9411-a5f95e9bbbda

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_transitionMap_of_isPullback_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def


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
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ b : ℕ, ∀ hb : b ≤ L,
      IsPullback (σ b hb) (t.projectionToBase b) (s.projectionToBase b) g := by
  intro b hb
  have hA := isPullback_transitionMap_of_isPullback_blowupMorphism t s L σ hstep 0 b (Nat.zero_le b) hb
  have hsq : CommSq t.isoZero.hom (σ 0 ((Nat.zero_le b).trans hb)) g s.isoZero.hom :=
    ⟨hzero.symm⟩
  have hB : IsPullback (σ 0 ((Nat.zero_le b).trans hb)) t.isoZero.hom s.isoZero.hom g :=
    (IsPullback.of_horiz_isIso hsq).flip
  rw [t.projectionToBase_def b, s.projectionToBase_def b]
  exact hA.paste_vert hB
end FunctorialResolution.EmbeddedResolution
