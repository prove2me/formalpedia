-- Prove2me | solution 1 for Formalism.L2.Pj.gsv_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:39.697416+00:00
-- url     : https://prove2.me/submissions/94209994-4d18-4c37-898a-f5da03dcff5b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecV
import Theorems.Thm_Formalism_L2_Pj_gsv_hcId
import Theorems.Thm_Formalism_L2_Pj_gsv_rel
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_one
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_pre
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_uniq_w
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart scaleD)
open Formalism.L2.Pj.GSR (Rel viaT liftT)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [CommRing L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
namespace Formalism.L2.Pj
theorem _root_.solution (hx : IsUnivChart _ n xc) (cc : Fin n → L) : IsTanAt x (gsvVec x xc cc) := by
  refine ⟨gsvVec_w cc, ?_⟩
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  have ht : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc = 1 :=
    ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc
  have hr := Formalism.L2.Pj.GSR.rel_pre
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) (gsv_rel xc cc)
  rw [ht] at hr
  have h1 : Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫
      gsvW xc cc = 1 := by
    first
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hc htk hr (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hc hr (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hr (Formalism.L2.Pj.GSR.rel_one hc htk)
  calc spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ gsvVec x xc cc
      = (Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫
          gsvW xc cc).left := rfl
    _ = (1 : _ ⟶ Xo.univ.t.G).left := congrArg Over.Hom.left h1
    _ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
      let e : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) ⟶ Over.mk x :=
        Over.homMk (𝟙 _) (by simp [ReciprocityTheory.ChartRestriction.G.Chart.sp])
      rw [← comp_one e]
      simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]
      try rfl
end Formalism.L2.Pj
