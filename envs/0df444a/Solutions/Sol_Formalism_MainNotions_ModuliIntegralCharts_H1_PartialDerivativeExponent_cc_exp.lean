-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.cc_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:21.544638+00:00
-- url     : https://prove2.me/submissions/1fdf144b-025a-4406-a01c-5b061d715b15

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
theorem _root_.solution {τ : Type} (x : MvPowerSeries τ k) (hx : constantCoeff x = 0) :
    constantCoeff (PowerSeries.subst x (PowerSeries.exp k)) = 1 := by
  have hx' := PowerSeries.HasSubst.of_constantCoeff_zero hx
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst hx', finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro d hd
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hx, zero_pow hd, smul_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
