-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.prod_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:25:38.387498+00:00
-- url     : https://prove2.me/submissions/7c9ea5b5-723d-48b4-933e-8bd89f4f4751

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
theorem _root_.solution {τ : Type} [Algebra ℚ R] : ∀ (n : ℕ) (q : Fin n → MvPowerSeries τ R),
    (∀ b, MvPowerSeries.constantCoeff (q b) = 0) →
    ∏ b, PowerSeries.subst (q b) (PowerSeries.exp R) = PowerSeries.subst (∑ b, q b) (PowerSeries.exp R)
  | 0, q, _ => by rw [Fin.prod_univ_zero, Fin.sum_univ_zero, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  | n + 1, q, hq => by
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, solution n (fun b => q b.succ) (fun b => hq _),
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (ha := hq 0)
        (hb := by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hq _)]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
