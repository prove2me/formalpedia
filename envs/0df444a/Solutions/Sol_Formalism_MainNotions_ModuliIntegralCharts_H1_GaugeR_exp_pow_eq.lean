-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.exp_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:05.165473+00:00
-- url     : https://prove2.me/submissions/aa5b82c6-5a15-41e2-a71c-190e1dc0c53f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeExpPow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_cc_smul_q
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
    (hq : MvPowerSeries.constantCoeff q = 0) : ∀ k : ℕ,
    PowerSeries.subst q (PowerSeries.exp S) ^ k = PowerSeries.subst ((k : S) • q) (PowerSeries.exp S)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_smul, exp_zero]
  | k + 1 => by
    rw [pow_succ, solution q hq k, ← exp_add (ha := cc_smul_q hq (k : S)) (hb := hq), Nat.cast_succ, add_smul,
      one_smul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
