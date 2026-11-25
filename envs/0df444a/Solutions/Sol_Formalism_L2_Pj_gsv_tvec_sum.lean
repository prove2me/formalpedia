-- Prove2me | solution 1 for Formalism.L2.Pj.gsv_tvec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:46.226952+00:00
-- url     : https://prove2.me/submissions/4f9e4d57-8742-4728-b9cc-c3c746f49065

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
theorem _root_.solution (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → L) (e : Fin m → Fin n → L) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  induction m with
  | zero =>
    simp only [Fin.sum_univ_zero, List.ofFn_zero, List.prod_nil]
    have h := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → L) 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx,
      List.ofFn_succ, List.prod_cons, ih (fun j => a j.succ) (fun j => e j.succ)]
end Formalism.L2.Pj
