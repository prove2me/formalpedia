-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.expOfChart_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:57.046115+00:00
-- url     : https://prove2.me/submissions/1ce368b1-0f4d-4cf4-82fc-6305f975ffcc

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution (h1 : ExpChartOfSt) (h2 : ExpGaugeOfSt) : ExpOfChartSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C hT
  obtain ⟨φ, hφ, hx⟩ := h1 E H Dw l Xo c S y C
  exact ⟨φ, hφ, hx, h2 E H Dw l Xo c hs S y C hT φ hφ hx⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1
