-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.gaugeUniq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:30.462379+00:00
-- url     : https://prove2.me/submissions/c361bf7d-1d51-44e2-98e2-905f0907c92e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqD
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeExpPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqPf
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_gaugeUniq_of__2db4fcf18649
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_exp_pow_mul_exp_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_gaugeRatio


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
theorem _root_.solution (hB : BetaUniqSt) : GaugeUniqSt :=
  GaugeR.gaugeUniq_of' hB GRPf.gaugeRatio fun _ _ _ _ q hq k => GaugeR.exp_pow_mul_exp_neg q hq k
end Formalism.MainNotions.ModuliIntegralCharts.H1
