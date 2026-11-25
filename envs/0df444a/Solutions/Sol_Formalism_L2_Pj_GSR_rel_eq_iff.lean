-- Prove2me | solution 1 for Formalism.L2.Pj.GSR.rel_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:26:53.220951+00:00
-- url     : https://prove2.me/submissions/4674940f-e900-41e8-be0f-9479a3d50630

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_uniq_w
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_uniq_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_uniq_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_uniq_w


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
  (hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {k : Type} [CommRing k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
include hc
namespace Formalism.L2.Pj.GSR
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} {w₁ w₂ : viaT tk X ⟶ G'} {v₁ v₂ : X ⟶ (Over.pullback g).obj G}
    (h₁ : Rel (F := F) tk g w₁ v₁) (h₂ : Rel (F := F) tk g w₂ v₂) : w₁ = w₂ ↔ v₁ = v₂ := by
  constructor
  · rintro rfl
    exact Formalism.L2.Pj.GSR.rel_uniq_v h₁ h₂
  · rintro rfl
    exact Formalism.L2.Pj.GSR.rel_uniq_w hc h₁ h₂
end Formalism.L2.Pj.GSR
