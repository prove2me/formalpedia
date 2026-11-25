-- Prove2me | solution 1 for Formalism.L2.Pj.gfp_tvec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:59.705073+00:00
-- url     : https://prove2.me/submissions/c96a07f2-92e3-450a-9575-e460048db00e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart Rel viaT liftT scaleD)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
namespace Formalism.L2.Pj
theorem _root_.solution (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → L) (e : Fin m → Fin n → L) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  have h0 : tvec (x := xc) (0 : Fin n → L) = 1 := by
    have e0 := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → L) 0
    rw [add_zero] at e0
    simpa using e0.symm
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ← ih, Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx]
end Formalism.L2.Pj
