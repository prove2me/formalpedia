-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.cc_smul_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:48.8278+00:00
-- url     : https://prove2.me/submissions/3cd5b5e7-2528-4cba-82cd-28d8f0fdbb3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeExpPow

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution {S σ : Type} [CommRing S] {q : MvPowerSeries σ S} (hq : MvPowerSeries.constantCoeff q = 0)
    (r : S) : MvPowerSeries.constantCoeff (r • q) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq, mul_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
