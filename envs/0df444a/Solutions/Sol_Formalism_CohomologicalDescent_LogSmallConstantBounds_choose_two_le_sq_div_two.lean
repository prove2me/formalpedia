-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.choose_two_le_sq_div_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:57.027283+00:00
-- url     : https://prove2.me/submissions/0e1093ac-5186-4c68-8baa-7ada3247195b

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds

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
theorem _root_.solution (n : ℕ) : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
  have h1 : 2 * n.choose 2 ≤ n ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (n * (n - 1) / 2) = (n * (n - 1) / 2) * 2 := by ring
      _ ≤ n * (n - 1) := Nat.div_mul_le_self _ _
      _ ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = n ^ 2 := by ring
  have h2 : (2 : ℝ) * (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h1
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
