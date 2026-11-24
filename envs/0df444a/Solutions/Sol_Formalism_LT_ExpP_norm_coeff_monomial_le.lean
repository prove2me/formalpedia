-- Prove2me | solution 1 for Formalism.LT.ExpP.norm_coeff_monomial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:58.052818+00:00
-- url     : https://prove2.me/submissions/3e6672bf-8f30-4b2b-8c63-8923e9381370

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.ExpP
theorem _root_.solution (m k : ℕ) (e : Fin 2 →₀ ℕ) :
    ‖MvPowerSeries.coeff e
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * MvPowerSeries.X 1 ^ k)‖ ≤ 1 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one,
    MvPowerSeries.coeff_monomial]
  split_ifs <;> simp
end Formalism.LT.ExpP
