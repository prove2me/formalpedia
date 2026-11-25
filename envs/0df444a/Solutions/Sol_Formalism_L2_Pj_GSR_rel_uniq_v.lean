-- Prove2me | solution 1 for Formalism.L2.Pj.GSR.rel_uniq_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:09:32.286837+00:00
-- url     : https://prove2.me/submissions/1c438146-415d-4628-8b60-53bf7131b771

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
namespace Formalism.L2.Pj.GSR
theorem _root_.solution {X : Over (Spec (CommRingCat.of k))} {w : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w v') : v = v' := by
  have e : v.left ≫ pullback.fst G.hom g = v'.left ≫ pullback.fst G.hom g :=
    (h : _ = v.left ≫ pullback.fst G.hom g).symm.trans (h' : _ = v'.left ≫ pullback.fst G.hom g)
  refine Over.OverMorphism.ext (pullback.hom_ext e ?_)
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v
  have hv' : v'.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v'
  rw [hv, hv']
end Formalism.L2.Pj.GSR
