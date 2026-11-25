-- Prove2me | solution 1 for Formalism.L2.Pj.gsv_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:35.880391+00:00
-- url     : https://prove2.me/submissions/f3db60ab-3ad6-42ab-866b-ef078339abe9

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecV
import Theorems.Thm_Formalism_L2_Pj_gsv_hcId
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_exists_v
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_one
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_pre
import Theorems.Thm_Formalism_L2_Pj_GSR_rel_uniq_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_uniq_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec


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
theorem _root_.solution (hx : IsUnivChart _ n xc) (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) :
    ∃ cc, w = gsvVec x xc cc := by
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let W : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G := Over.homMk w hw.1
  obtain ⟨v, hv⟩ : ∃ v, Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x W v := by
    first
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc htk W
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc htk
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc W
    | exact Formalism.L2.Pj.GSR.rel_exists_v W
  have hone : Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫ W = 1 := by
    apply Over.OverMorphism.ext
    let e : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) ⟶ Over.mk x :=
      Over.homMk (𝟙 _) (by simp [ReciprocityTheory.ChartRestriction.G.Chart.sp])
    rw [← comp_one e]
    simp only [e, W, Formalism.L2.Pj.GSR.liftT, Over.comp_left, Over.homMk_left, Category.id_comp]
    exact hw.2
  have hv1 := Formalism.L2.Pj.GSR.rel_pre (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) hv
  rw [hone] at hv1
  have htan : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ v = 1 := by
    first
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hc htk hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hc hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v htan, ?_⟩
  have hs := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v htan
  have hv' : w ≫ 𝟙 _ = v.left ≫ pullback.fst Xo.univ.t.G.hom x := hv
  rw [Category.comp_id] at hv'
  rw [hv']
  exact congrArg (fun f => f.left ≫ pullback.fst Xo.univ.t.G.hom x) hs
end Formalism.L2.Pj
