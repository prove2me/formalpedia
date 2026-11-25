-- Prove2me | solution 1 for Formalism.BehrendSets.Sums.linB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:25:10.56936+00:00
-- url     : https://prove2.me/submissions/9b6ab923-f75f-41ce-bbb2-49862da3b8fd

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoLeCastOfTwoLe
import Theorems.Thm_Formalism_BehrendSets_Sums_linB_real
import Theorems.Thm_Formalism_BehrendSets_Sums_castB
import Theorems.Thm_Formalism_BehrendSets_Sums_hK1
import Theorems.Thm_Formalism_BehrendSets_Sums_two_le_cast_of_two_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Sums
namespace Formalism.BehrendSets.Sums
theorem _root_.solution (M k : ℕ) (L : ℝ) (hM : 2 ≤ M) (hL : 0 ≤ L) :
    L / (((M * (k + 1) - 1 : ℕ)) : ℝ) ≤ 2 * L * (1 / ((k : ℝ) + 1)) / (M : ℝ) := by
  rw [castB M k hM]
  exact linB_real _ _ _ (two_le_cast_of_two_le M hM) (hK1 k) hL
end Formalism.BehrendSets.Sums
