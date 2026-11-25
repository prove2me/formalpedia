-- Prove2me | solution 1 for Formalism.L2.Pj.gfpVec_tmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:33.714893+00:00
-- url     : https://prove2.me/submissions/284a1ed4-e3f8-48e3-a8b4-fe03c77e0f1d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
namespace Formalism.L2.Pj
theorem _root_.solution (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    gfpVec x xc (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      gfpVec x xc cc ≫ (Xo.univ.t.act.act a).left := by
  have ht : tvec (x := xc) (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a) := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx _ cc
    | exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx _ cc).symm
    | exact (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx
        (tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a)) _).symm
  have e1 : ((Over.pullback x).map (Xo.univ.t.act.act a)).left ≫ pullback.fst Xo.univ.t.G.hom x =
      pullback.fst Xo.univ.t.G.hom x ≫ (Xo.univ.t.act.act a).left := by
    simp
    first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]
    | (rw [limit.lift_π]; rfl)
  simp only [gfpVec, ht, Over.comp_left, Category.assoc, e1]
end Formalism.L2.Pj
