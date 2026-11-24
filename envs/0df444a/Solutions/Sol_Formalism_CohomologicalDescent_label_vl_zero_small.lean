-- Prove2me | solution 1 for Formalism.CohomologicalDescent.label_vl_zero_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:48.913799+00:00
-- url     : https://prove2.me/submissions/702fcce1-6e8b-410e-81cd-90c1f38deff8

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse

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
theorem _root_.solution {l : ℕ} {n : ℤ} (h0 : 0 < n) (h1 : n < l) : vl l n = 0 := by
  show padicValInt l n = 0
  apply padicValInt.eq_zero_of_not_dvd
  intro hd
  have := Int.le_of_dvd h0 hd
  linarith
end Formalism.CohomologicalDescent
