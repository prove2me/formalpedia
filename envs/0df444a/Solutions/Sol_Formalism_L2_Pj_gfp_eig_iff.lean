-- Prove2me | solution 1 for Formalism.L2.Pj.gfp_eig_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:44:33.564281+00:00
-- url     : https://prove2.me/submissions/8252731b-85d2-4a45-b315-580d1dad8ab2

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Theorems.Thm_Formalism_L2_Pj_gfp_hcId
import Theorems.Thm_Formalism_L2_Pj_gfp_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_mem_eigLat_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff


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
theorem _root_.solution [Algebra c.F L] (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) (cc : Fin n → L) :
    IsEigAt c τ (gfpVec x xc cc) ↔
      cc ∈ eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a)) := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
  refine forall_congr' fun a => ?_
  rw [← ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff hx]
  exact ReciprocityTheory.ChartRestriction.G.Chart.eig_iff gfp_hcId (Xo.univ.t.act.act a) (Xo.univ.t.act.act a)
    (by rw [Category.comp_id, Category.id_comp]) _ (gfp_rel xc cc)
end Formalism.L2.Pj
