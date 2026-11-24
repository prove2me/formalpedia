-- Prove2me | solution 1 for Formalism.CohomologicalDescent.sums_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:02.433362+00:00
-- url     : https://prove2.me/submissions/0273bdc0-b7b2-4fa1-9a43-7ead40b64d1c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse

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
theorem _root_.solution (F : ℝ → ℝ) (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, (F (d : ℝ) - F ((d : ℝ) - 1)) = F n - F 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    rw [add_sub_cancel_right]
    ring
end Formalism.CohomologicalDescent
