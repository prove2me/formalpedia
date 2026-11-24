-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.anti_of_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:41.591074+00:00
-- url     : https://prove2.me/submissions/488f9efd-5530-4306-b2bd-77061b066c02

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_VandNSuccRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (f : ℕ → ℝ) (N : ℕ) (h : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i j, i < j → j < N → f j < f i := by
  intro i j hij hjN
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (h j (by omega)) (ih h' (by omega))
    · subst h'; exact h i hjN
end Formalism.LogVandermondeBounds.StandardLattice
