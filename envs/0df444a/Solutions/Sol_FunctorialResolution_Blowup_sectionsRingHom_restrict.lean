-- Prove2me | solution 1 for FunctorialResolution.Blowup.sectionsRingHom_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:14:14.473429+00:00
-- url     : https://prove2.me/submissions/846f4fec-d333-46c7-933b-bb7360c34ac1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u
namespace FunctorialResolution.Blowup
theorem _root_.solution {A : Type u} [CommRing A] {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of A)) {V V' : W.Opens} (hV : V' ≤ V) (r : A) :
    sectionsRingHom g V' r =
      (W.presheaf.map (homOfLE hV).op).hom (sectionsRingHom g V r) := by
  have hmap : W.presheaf.map
        (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V' ≤ g ⁻¹ᵁ ⊤)).op
      = W.presheaf.map
          (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op ≫
        W.presheaf.map (homOfLE hV).op :=
    W.presheaf.map_comp
      (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op
      (homOfLE hV).op
  have key : g.appLE ⊤ V' (le_top.trans (Scheme.Hom.preimage_top g).ge) =
      g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge) ≫
        W.presheaf.map (homOfLE hV).op := by
    show g.app ⊤ ≫ W.presheaf.map
          (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V' ≤ g ⁻¹ᵁ ⊤)).op
        = (g.app ⊤ ≫ W.presheaf.map
            (homOfLE (le_top.trans (Scheme.Hom.preimage_top g).ge : V ≤ g ⁻¹ᵁ ⊤)).op) ≫
          W.presheaf.map (homOfLE hV).op
    rw [Category.assoc, ← hmap]
  exact congrArg
    (fun φ : Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)) ⟶ Γ(W, V') =>
      φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)) key
end FunctorialResolution.Blowup
