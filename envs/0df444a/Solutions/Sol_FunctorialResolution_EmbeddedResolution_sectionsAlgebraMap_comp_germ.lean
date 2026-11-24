-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.sectionsAlgebraMap_comp_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:15.158136+00:00
-- url     : https://prove2.me/submissions/33538f68-97c6-4d75-a277-7179688d3eb7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal



set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.comp (sectionsAlgebraMap k p U) = stalkAlgebraMap k p x := by
  have hle : U ≤ (⊤ : X.Opens) := le_top
  have key : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ U x hx
      = X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x) := by
    simp
  have key' : (X.presheaf.germ U x hx).hom.comp (X.presheaf.map (homOfLE hle).op).hom
      = (X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)).hom := by
    rw [← CommRingCat.hom_comp, key]
  show (X.presheaf.germ U x hx).hom.comp (sectionsAlgebraMap k p U)
      = (X.presheaf.germ (⊤ : X.Opens) x (Opens.mem_top x)).hom.comp (sectionsAlgebraMap k p ⊤)
  rw [← key', RingHom.comp_assoc, sectionsAlgebraMap_comp_restrict k p hle]
end FunctorialResolution.EmbeddedResolution
