-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.gaugeUniq_of_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:53.448284+00:00
-- url     : https://prove2.me/submissions/85228072-2f74-4881-a47c-75ed18c11126

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqD
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeExpPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_gaugeUniq_of
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_betaUniq_of_global


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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution (hG : GlobalFnsSt) : GaugeUniqSt :=
  gaugeUniq_of (betaUniq_of_global hG)
end Formalism.MainNotions.ModuliIntegralCharts.H1
