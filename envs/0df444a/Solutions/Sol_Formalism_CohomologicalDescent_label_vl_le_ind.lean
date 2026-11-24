-- Prove2me | solution 1 for Formalism.CohomologicalDescent.label_vl_le_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:50:01.004848+00:00
-- url     : https://prove2.me/submissions/14238c06-c7f8-42a7-bcdf-965a80a1c388

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Theorems.Thm_Formalism_CohomologicalDescent_label_vl_le_one

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
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution {l : ℕ} (hl : l.Prime) {n : ℤ} (h0 : 0 < n) (h1 : n < (l : ℤ) ^ 2) :
    (vl l n : ℝ) ≤ if (l : ℤ) ∣ n then 1 else 0 := by
  split_ifs with hd
  · exact_mod_cast label_vl_le_one hl h0 h1
  · have h : vl l n = 0 := padicValInt.eq_zero_of_not_dvd hd
    simp [h]
end Formalism.CohomologicalDescent
