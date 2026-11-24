-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH.sA_ptm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:03.704392+00:00
-- url     : https://prove2.me/submissions/58ba6e46-c86f-4109-bcd7-172c75d7e8de

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_jetSubstP_actP
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const_actPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
theorem _root_.solution (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (u : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c u)) ≫ ptm C P m =
      ptm C (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) (P i j)) m := by
  unfold ptm
  rw [GermD.homAt_comp, jetSubstP_actP,
    ExpGF.jetSubstPS_comp m (fun p : Fin n × Fin C.d => P p.1 p.2) (actPS (Dw := Dw) (S := S) c u)
      (fun p => hP p.1 p.2) (const_actPS c u)]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
