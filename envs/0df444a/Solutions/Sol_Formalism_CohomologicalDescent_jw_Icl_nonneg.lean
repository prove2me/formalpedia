-- Prove2me | solution 1 for Formalism.CohomologicalDescent.jw_Icl_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:13.128512+00:00
-- url     : https://prove2.me/submissions/433f0051-8e3f-45c3-97ee-97541f45026d

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_StatementC
import Definitions.Def_Formalism_PieriBlockIdeals_JointCW5
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Theorems.Thm_Formalism_CohomologicalDescent_jw_Il_eq

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
open Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.CohomologicalDescent
theorem _root_.solution {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : 0 ≤ D.Icl τ l := by
  rw [← jw_Il_eq]
  unfold IlInd
  split_ifs <;> norm_num
end Formalism.CohomologicalDescent
