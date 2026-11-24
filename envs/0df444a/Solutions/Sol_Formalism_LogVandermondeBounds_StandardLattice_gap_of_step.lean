-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.gap_of_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:46.368595+00:00
-- url     : https://prove2.me/submissions/df6acff5-5169-4c47-8a51-eaa2ed33e367

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
theorem _root_.solution (f : ℕ → ℝ) (N : ℕ) (h : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i) :
    ∀ i j, i < j → j < N → 1 ≤ f j - f i := by
  intro i j hij hjN
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · have h1 := h j (by omega)
      have h2 := ih h' (by omega)
      linarith
    · subst h'; exact h i hjN
end Formalism.LogVandermondeBounds.StandardLattice
