-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.eval_expSeries_neg_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:58.621584+00:00
-- url     : https://prove2.me/submissions/2c1bf44e-5a94-4d97-bf95-97e872c71b61

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_const_bilL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_diag_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {O : Type} [CommRing O] [StarRing O]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
theorem _root_.solution (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) :
    ev (n := 1) ![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)] (expP (-bilL B.G cc)) =
      expP (-diagL B w0 cc) := by
  have ha : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d =>
      (![pt S (n := 1) d 0, comp1 (B.A.act w0) (pt S (n := 1) d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) :=
    ⟨fun p => by rw [diag_const B w0 p.1 p.2]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hb : MvPowerSeries.HasSubst (fun _ : Unit => -bilL B.G cc) :=
    ⟨fun _ => by rw [map_neg, const_bilL, neg_zero]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  unfold Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.expP ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply hb ha]
  congr 1
  funext _
  rw [← MvPowerSeries.coe_substAlgHom ha, map_neg, MvPowerSeries.coe_substAlgHom]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
