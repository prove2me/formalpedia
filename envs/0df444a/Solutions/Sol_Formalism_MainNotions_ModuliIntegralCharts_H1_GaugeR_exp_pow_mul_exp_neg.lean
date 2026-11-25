-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.exp_pow_mul_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:56.011097+00:00
-- url     : https://prove2.me/submissions/db151b5f-29c2-4c46-b40e-104d5fd7f3dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeExpPow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_cc_smul_q
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_exp_pow_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero


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
theorem _root_.solution {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) (k : ℕ) :
    PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1 := by
  have hneg : MvPowerSeries.constantCoeff (-((k : S) • q)) = 0 := by
    rw [map_neg, cc_smul_q hq, neg_zero]
  rw [exp_pow_eq q hq k, ← exp_add (cc_smul_q hq _) hneg, add_neg_cancel, exp_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
