-- Prove2me | solution 1 for Formalism.L2.Pj.GSR.rel_uniq_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:45.31397+00:00
-- url     : https://prove2.me/submissions/89852707-acca-4ef2-83a0-c1c25dd87dec

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
include hc
namespace Formalism.L2.Pj.GSR
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v) : w = w' := by
  have e : w.left ≫ F = w'.left ≫ F :=
    (h : w.left ≫ F = _).trans (h' : w'.left ≫ F = _).symm
  exact Over.OverMorphism.ext (hc.1.hom_ext e (by rw [Over.w w, Over.w w']))
end Formalism.L2.Pj.GSR
