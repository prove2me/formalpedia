-- Prove2me | solution 1 for Formalism.L2.Pj.GSR.rel_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:03.899011+00:00
-- url     : https://prove2.me/submissions/c4b3ef0d-9822-44fe-a2dc-850f7431ab08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_act


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
theorem _root_.solution (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) {X : Over (Spec (CommRingCat.of k))}
    {w : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) :
    Rel (F := F) tk g (w ≫ a) (v ≫ (Over.pullback g).map b) := by
  have h' : w.left ≫ F = v.left ≫ pullback.fst G.hom g := h
  show (w ≫ a).left ≫ F = (v ≫ (Over.pullback g).map b).left ≫ pullback.fst G.hom g
  first
  | (simp [hab, reassoc_of% h']; erw [pullback.lift_fst])
  | exact ReciprocityTheory.ChartRestriction.G.Chart.rel_act (F := F) a b hab (show ReciprocityTheory.ChartRestriction.G.Chart.Rel (F := F) tk g w v from h)
end Formalism.L2.Pj.GSR
