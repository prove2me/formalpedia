-- Prove2me | solution 1 for Formalism.LT.InvIntP.Low.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:02.078062+00:00
-- url     : https://prove2.me/submissions/e756fcf4-39f2-41f2-807c-25b82b3550bc

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt

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
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.LT.InvIntP
namespace Low
theorem _root_.solution {m k : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) (x * y) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ab hab => ?_
  have hab' : ab.1 + ab.2 = d := by simpa using hab
  have hdeg : ab.1.degree + ab.2.degree = d.degree := by rw [← hab', map_add]
  by_cases h1 : ab.1.degree < m
  · rw [hx _ h1, zero_mul]
  · rw [hy _ (by omega), mul_zero]
end Low
end Formalism.LT.InvIntP
