-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.expS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:56.653117+00:00
-- url     : https://prove2.me/submissions/8d4d9bac-4b88-4b4c-9083-a26c991ac7ed

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_exp_biv
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_psubst_comp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
open MvPowerSeries
variable {σ : Type}
variable {k : Type} [CommRing k]
variable [Algebra ℚ k]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
theorem _root_.solution {τ : Type} (x y : MvPowerSeries τ k) (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    PowerSeries.subst (x + y) (PowerSeries.exp k) =
      PowerSeries.subst x (PowerSeries.exp k) * PowerSeries.subst y (PowerSeries.exp k) := by
  have hb : HasSubst (![x, y] : Fin 2 → MvPowerSeries τ k) :=
    hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])
  have h := congrArg (subst (![x, y] : Fin 2 → MvPowerSeries τ k)) (exp_biv (k := k))
  rw [psubst_comp _ hb (X 0 + X 1) (by simp), subst_mul hb, psubst_comp _ hb (X 0) (by simp),
    psubst_comp _ hb (X 1) (by simp)] at h
  simpa [subst_add hb, subst_X hb] using h
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
