-- Prove2me | solution 1 for Formalism.L2.Pj.GSR.rel_exists_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:20:43.843118+00:00
-- url     : https://prove2.me/submissions/3835d81c-d6ed-4c6c-9208-1cd65603dac9

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
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} (v : X ⟶ (Over.pullback g).obj G) :
    ∃ w : viaT tk X ⟶ G', Rel (F := F) tk g w v := by
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v
  have cond : (v.left ≫ pullback.fst G.hom g) ≫ G.hom = (X.hom ≫ tk) ≫ f := by
    rw [Category.assoc, pullback.condition, reassoc_of% hv, Category.assoc, hg]
  exact ⟨Over.homMk (hc.1.lift _ _ cond) (hc.1.lift_snd _ _ cond), hc.1.lift_fst _ _ cond⟩
end Formalism.L2.Pj.GSR
