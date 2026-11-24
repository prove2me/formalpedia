-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.iso_hom_comp_transitionMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:38.687939+00:00
-- url     : https://prove2.me/submissions/de304085-1ae2-46bf-99f8-9d8d10a231d8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_self
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem transitionMap_self {X : Scheme.{u}} (u : SequenceOfBlowups X) {a : ℕ}
    (h : a ≤ a) : u.transitionMap h = 𝟙 (u.schemeAt a) := by
  have h0 : (CategoryTheory.homOfLE h).op = 𝟙 (Opposite.op a) := rfl
  rw [u.transitionMap_def, h0, CategoryTheory.Functor.map_id]
namespace IsStrictPullbackBlowupSeq
end IsStrictPullbackBlowupSeq
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups
theorem _root_.solution {X : Scheme.{u}} (s t : SequenceOfBlowups X) (L : ℕ)
    (e : ∀ i : ℕ, i ≤ L → (s.schemeAt i ≅ t.schemeAt i))
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      (e (i + 1) hi).hom ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ (e i hi.le).hom) :
    ∀ a b : ℕ, ∀ hab : a ≤ b, ∀ hb : b ≤ L,
      (e b hb).hom ≫ t.transitionMap hab = s.transitionMap hab ≫ (e a (hab.trans hb)).hom := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
      intro hb
      have ht : t.transitionMap (le_refl a) = 𝟙 (t.schemeAt a) := transitionMap_self t (le_refl a)
      have hs : s.transitionMap (le_refl a) = 𝟙 (s.schemeAt a) := transitionMap_self s (le_refl a)
      rw [ht, hs, Category.comp_id, Category.id_comp]
  | succ n hn ih =>
      intro hb
      have hn' : n ≤ L := Nat.le_of_succ_le hb
      have h1 : n ≤ n + 1 := Nat.le_succ n
      rw [← t.transitionMap_trans hn h1, ← s.transitionMap_trans hn h1, ← t.blowupMorphism_eq_transitionMap n,
        ← s.blowupMorphism_eq_transitionMap n, ← Category.assoc, hstep n hb, Category.assoc, ih hn']
      simp
end SequenceOfBlowups
end FunctorialResolution.EmbeddedResolution
