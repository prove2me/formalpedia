-- Prove2me | solution 1 for Formalism.LT.ExpP.norm_finsum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:56.43636+00:00
-- url     : https://prove2.me/submissions/57774260-7b52-4ae2-819e-f167043b8e7b

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
theorem _root_.solution {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  by_cases h : (Function.support g).Finite
  · rw [finsum_eq_sum g h]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support h, norm_zero]
    exact hC
end Formalism.LT.ExpP
