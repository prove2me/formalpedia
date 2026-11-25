-- Prove2me | solution 1 for Formalism.L2.Pj.GSR.rel_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:40:18.764203+00:00
-- url     : https://prove2.me/submissions/728dbcbe-8c7c-4a56-88c2-ce6507d57dc6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GSR
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [CommRing k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)
variable {tk g}
namespace Formalism.L2.Pj.GSR
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) :
    Rel (F := F) tk g w v ↔
      pushPt (isGrpPullback_pullback G g).1.w v = iota2 hg X ≫ pushPt hc.1.w w := by
  constructor
  · intro h
    ext
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp]
    exact (h : w.left ≫ F = _).symm
  · intro h
    have e : (pushPt (isGrpPullback_pullback G g).1.w v).left = (iota2 hg X ≫ pushPt hc.1.w w).left := by
      rw [h]
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp] at e
    exact e.symm
end Formalism.L2.Pj.GSR
