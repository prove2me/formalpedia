-- Prove2me | solution 1 for Formalism.L2.Pj.gfp_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:42:16.851829+00:00
-- url     : https://prove2.me/submissions/bb0aa71d-a4f5-408e-aa41-9e83e7dd6c87

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj


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
theorem _root_.solution (hx : IsUnivChart _ n xc) {c₁ c₂ : Fin n → L} (h : gfpVec x xc c₁ = gfpVec x xc c₂) : c₁ = c₂ := by
  have hw : ∀ c : Fin n → L,
      (tvec (x := xc) c).left ≫ pullback.snd Xo.univ.t.G.hom x = spMap (algebraMap L (DualNumber L)) :=
    fun c => by simpa using Over.w (tvec (x := xc) c)
  have h' : (tvec (x := xc) c₁).left ≫ pullback.fst Xo.univ.t.G.hom x =
      (tvec (x := xc) c₂).left ≫ pullback.fst Xo.univ.t.G.hom x := h
  have ht : tvec (x := xc) c₁ = tvec (x := xc) c₂ :=
    Over.OverMorphism.ext (pullback.hom_ext h' (by rw [hw, hw]))
  first
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx ht
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj ht
end Formalism.L2.Pj
