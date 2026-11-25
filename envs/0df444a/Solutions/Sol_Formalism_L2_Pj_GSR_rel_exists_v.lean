-- Prove2me | solution 1 for Formalism.L2.Pj.GSR.rel_exists_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:43.32446+00:00
-- url     : https://prove2.me/submissions/af3228fe-4ffc-4e55-9980-e6b552b77c07

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel

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
include hc hg
namespace Formalism.L2.Pj.GSR
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by
  have hw : w.left ≫ G'.hom = X.hom ≫ tk := Over.w w
  have cond : (w.left ≫ F) ≫ G.hom = X.hom ≫ g := by
    rw [Category.assoc, hc.1.w, reassoc_of% hw, hg]
  exact ⟨Over.homMk (pullback.lift _ _ cond) (pullback.lift_snd _ _ cond), (pullback.lift_fst _ _ cond).symm⟩
end Formalism.L2.Pj.GSR
