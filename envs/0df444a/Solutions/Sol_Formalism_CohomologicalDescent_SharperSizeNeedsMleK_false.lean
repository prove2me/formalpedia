-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SharperSizeNeedsMleK_false
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:21.452849+00:00
-- url     : https://prove2.me/submissions/13d390e0-a898-4a56-9f40-4da3e9da0125

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
theorem _root_.solution : ¬ SharperSizeNeedsMleK := by
  intro H
  have key := H 1 2 1 (by norm_num) (by norm_num) (by norm_num)
  have h1 : ∑ d ∈ Finset.Icc (1 : ℕ) 1, min ((1 : ℕ) : ℝ) ((((2 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) / (d : ℝ)) = 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton]
    norm_num
  have h2 : Real.log (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = - Real.log 2 := by
    push_cast
    rw [one_div, Real.log_inv]
  rw [h1, h2] at key
  have hl := Real.log_two_gt_d9
  push_cast at key
  linarith
end Formalism.CohomologicalDescent
