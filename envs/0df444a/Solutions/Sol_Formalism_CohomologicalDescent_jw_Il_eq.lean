-- Prove2me | solution 1 for Formalism.CohomologicalDescent.jw_Il_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:57.289192+00:00
-- url     : https://prove2.me/submissions/bdf9d2d5-6c63-45dc-b069-bad345418d24

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_StatementC
import Definitions.Def_Formalism_PieriBlockIdeals_JointCW5
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound

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
theorem _root_.solution {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) :
    IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) = D.Icl τ l := by
  unfold IlInd Data.Icl
  by_cases h : ∃ y : ℤ, D.xlo τ ≤ y ∧ y ≤ D.xhi τ ∧ (l : ℤ) ∣ y - D.maxB τ
  · rw [if_pos h]
  · rw [if_neg h]
end Formalism.CohomologicalDescent
