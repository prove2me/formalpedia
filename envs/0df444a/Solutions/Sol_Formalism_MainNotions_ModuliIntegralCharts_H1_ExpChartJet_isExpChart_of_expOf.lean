-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet.isExpChart_of_expOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:29:58.806198+00:00
-- url     : https://prove2.me/submissions/099a0341-745c-4377-99c7-a1dfae82ccac

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_xExp_zero
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_xExp_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_xExp_law
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_xExp_act
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_xExp_tan

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : IsExpOf C.B.G.F C.uvec φ) (hA : ExpActOf C φ) : IsExpChart y (xExp y C φ) where
  zero := xExp_zero C φ hφ
  trunc := xExp_trunc C φ
  law := xExp_law C φ hφ
  act := xExp_act C φ hφ hA
  tan := xExp_tan C φ hφ
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
