-- Prove2me | solution 1 for Formalism.LT.CoeffP.Bd.mul_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:05.409828+00:00
-- url     : https://prove2.me/submissions/e5081228-d93d-40fd-a834-2bb240e03458

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne

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
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
namespace Formalism.LT.CoeffP
namespace Bd
theorem _root_.solution {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (n : ℕ) :
    Bd (‖(n : K)‖ * a) (F * (n : MvPowerSeries ι K)) := by
  intro d
  rw [mul_comm F, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hF d) (norm_nonneg _)
end Bd
end Formalism.LT.CoeffP
