-- Prove2me | solution 1 for Formalism.L2.Pj.gfp_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:52.208799+00:00
-- url     : https://prove2.me/submissions/93fc6baf-525e-42a1-a4d1-b0df0b072a35

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart Rel viaT liftT scaleD)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
namespace Formalism.L2.Pj
theorem _root_.solution (hx : IsUnivChart _ n xc) (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) :
    ∃ cc, w = gfpVec x xc cc := by
  obtain ⟨hw1, hw2⟩ := hw
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L) ⟶ (Over.pullback x).obj Xo.univ.t.G :=
    Over.homMk (pullback.lift w (spMap (algebraMap L (DualNumber L))) hw1) (pullback.lift_snd _ _ hw1)
  have e2 : (pushHom (isGrpPullback_pullback Xo.univ.t.G x) (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) 1).left =
      (1 : Over.mk ((ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom ≫ x) ⟶ Xo.univ.t.G).left := by
    rw [map_one]
  change (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
    pullback.fst Xo.univ.t.G.hom x = _ at e2
  have e3 : (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
      pullback.fst Xo.univ.t.G.hom x = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    rw [e2, ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
    simp
  have hy : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y := by
    show ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y = 1
    ext
    apply pullback.hom_ext
    · rw [e3]
      change (spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫
        pullback.lift w (spMap (algebraMap L (DualNumber L))) hw1) ≫ pullback.fst Xo.univ.t.G.hom x = _
      rw [Category.assoc, pullback.lift_fst]
      exact hw2
    · have a1 : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y).left ≫ pullback.snd Xo.univ.t.G.hom x =
          (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom := by
        simpa using Over.w (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y)
      have a2 : (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
          pullback.snd Xo.univ.t.G.hom x = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom := by
        simpa using Over.w (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G)
      rw [a1, a2]
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy, ?_⟩
  have e : y = tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy) := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx y hy
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec y hy
  show w = (tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy)).left ≫ pullback.fst Xo.univ.t.G.hom x
  rw [← e]
  exact (pullback.lift_fst _ _ _).symm
end Formalism.L2.Pj
