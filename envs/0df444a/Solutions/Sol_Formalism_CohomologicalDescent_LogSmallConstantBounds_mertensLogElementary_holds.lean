-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.mertensLogElementary_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:58.873681+00:00
-- url     : https://prove2.me/submissions/a99e7c86-04d2-4907-9857-015d44f3422d

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_pr_eq_primesUpTo_floor
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_log_div_le_log_add_log_four

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : MertensLogElementary := by
  intro y hy
  rw [pr_eq_primesUpTo_floor]
  have hn : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hy)
  have h := sum_log_div_le_log_add_log_four ⌊y⌋₊ hn
  have h1 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hn
  have h2 := Real.log_le_log (by linarith) (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
