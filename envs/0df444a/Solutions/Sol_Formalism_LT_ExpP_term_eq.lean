-- Prove2me | solution 1 for Formalism.LT.ExpP.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:39.505568+00:00
-- url     : https://prove2.me/submissions/0c242980-8afe-420a-9c51-f2aa6b553154

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
theorem _root_.solution (p c : K) (d m : ℕ) :
    c • ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * (p • MvPowerSeries.X 1) ^ (d - m) *
      (d.choose m : MvPowerSeries (Fin 2) K)) =
    (c * (p ^ (d - m) * (d.choose m : K))) •
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * MvPowerSeries.X 1 ^ (d - m)) := by
  simp only [MvPowerSeries.smul_eq_C_mul, mul_pow, map_mul, map_pow, map_natCast]
  ring
end Formalism.LT.ExpP
