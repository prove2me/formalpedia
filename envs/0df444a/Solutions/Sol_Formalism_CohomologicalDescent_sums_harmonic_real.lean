-- Prove2me | solution 1 for Formalism.CohomologicalDescent.sums_harmonic_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:05.755938+00:00
-- url     : https://prove2.me/submissions/05acfa50-f055-446b-805a-df16b0c31436

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
theorem _root_.solution (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ≤ 1 + Real.log n := by
  have h1 := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h1
  push_cast at h1
  simpa [one_div] using h1
end Formalism.CohomologicalDescent
