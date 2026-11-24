-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.psubst_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:08.178892+00:00
-- url     : https://prove2.me/submissions/d0e94372-4c40-4927-a416-64237adc34b7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent

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
theorem _root_.solution {τ υ : Type} (b : τ → MvPowerSeries υ k) (hb : HasSubst b)
    (a : MvPowerSeries τ k) (ha : constantCoeff a = 0) (f : PowerSeries k) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hb]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
