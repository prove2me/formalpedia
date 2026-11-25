-- Prove2me | solution 1 for Formalism.L2.Pj.GSR.rel_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:57.299946+00:00
-- url     : https://prove2.me/submissions/13f1493e-4de7-4a43-820a-18d7381e9319

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
include hc hg
namespace Formalism.L2.Pj.GSR
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v') : Rel (F := F) tk g (w * w') (v * v') := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg] at h h' ⊢
  have e1 := map_mul (pushHom (isGrpPullback_pullback G g) X) v v'
  have e2 := map_mul ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X))) w w'
  exact e1.trans ((congrArg₂ (· * ·) h h').trans e2.symm)
end Formalism.L2.Pj.GSR
