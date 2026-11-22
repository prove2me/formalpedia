-- Prove2me | solution 1 for Formalism.LT.CoeffP.Bd.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:22.171728+00:00
-- url     : https://prove2.me/submissions/4f7da0a2-ce4c-40c9-b592-0ae56c9fc139

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
theorem _root_.solution {a b : ℝ} {F G : MvPowerSeries ι K} (hF : Bd a F) (hG : Bd b G) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : Bd (a * b) (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) (fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hF x.1) (hG x.2) (norm_nonneg _) ha
end Bd
end Formalism.LT.CoeffP
