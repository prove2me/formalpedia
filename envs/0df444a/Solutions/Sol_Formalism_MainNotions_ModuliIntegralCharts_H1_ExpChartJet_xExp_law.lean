-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.xExp_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:43:49.519368+00:00
-- url     : https://prove2.me/submissions/4fbf791d-d589-49d3-8282-809c4b404c46

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_j__copy_ce0f648d2468
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_j__law_514fb13dfa67
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution (hφ : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) :
    homAt y.x (jetSubstP m (addP (Dw := Dw) (S := S))) ≫ xExp y C φ m =
      jpt y (dL Dw) (xExp y C φ) m (0 : Fin 2) * jpt y (dL Dw) (xExp y C φ) m (1 : Fin 2) := by
  have e0 : ∀ i : Fin 2, jpt y (dL Dw) (xExp y C φ) m i =
      homAt y.x (jetSubstPS (m := m) (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2))) ≫ jpt y C.d C.x m i := by
    intro i
    rw [jpt, jpt, xExp, ← Category.assoc, GermD.homAt_comp, jφ_copy C φ hφ, ← GermD.homAt_comp, Category.assoc]
  rw [e0, e0, ← MonObj.comp_mul, ← C.chart.law m, xExp, ← Category.assoc, GermD.homAt_comp, jφ_law C φ hφ,
    ← GermD.homAt_comp, Category.assoc]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
