-- Prove2me | solution 1 for Formalism.LT.CoeffP.Bd.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:56.722481+00:00
-- url     : https://prove2.me/submissions/ca5624f7-9054-4e13-ab58-7c1f24719ea8

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mul
import Theorems.Thm_Formalism_LT_CoeffP_Bd_one

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
theorem _root_.solution {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (ha : 0 ≤ a) :
    ∀ n : ℕ, Bd (a ^ n) (F ^ n)
  | 0 => by simpa using (Bd.one : Bd 1 (1 : MvPowerSeries ι K))
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (solution hF ha n).mul hF (pow_nonneg ha n) ha
end Bd
end Formalism.LT.CoeffP
