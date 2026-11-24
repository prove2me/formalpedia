-- Prove2me | solution 1 for Formalism.CohomologicalDescent.leastCongruentPos_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:54.493195+00:00
-- url     : https://prove2.me/submissions/dade6f41-c261-45c4-9c7b-f1906e880a44

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
theorem _root_.solution {l : ℕ} (D : ℤ) (d : ℕ) (h1 : 1 ≤ d) (hd : (l : ℤ) ∣ D - d) : d0 l D ≤ d := by
  unfold d0
  exact Nat.sInf_le ⟨h1, hd⟩
end Formalism.CohomologicalDescent
