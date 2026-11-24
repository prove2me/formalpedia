-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_anti_of_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:29.147521+00:00
-- url     : https://prove2.me/submissions/ba6aef2c-a176-4cc4-9870-2694bc1e8bb6

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds

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
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases (show i < j ∨ i = j by omega) with h' | h'
    · exact lt_trans (h j hj) (ih h' (by omega))
    · subst h'; exact h i hj
end Formalism.LogVandermondeBounds.StandardLattice
