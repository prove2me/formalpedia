-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.mem_Iset_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:11.907931+00:00
-- url     : https://prove2.me/submissions/ef726691-8304-4835-8faf-19d5174ff025

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_term_le_B0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu' : Fin n → ℤ} {b : ℤ}
    (h' : Interlace lam nu') (hb : B0 lam nu' = b) (i : Fin n) : nu' i ∈ Iset lam b i := by
  have hle := term_le_B0 h' i
  have hi := h'.2 i
  have h1 : nu' i - lam i.succ ≤ min (len lam i) b :=
    le_min (by unfold len; linarith [hi.2]) (by rw [← hb]; exact hle)
  simp only [Iset, Finset.mem_Icc]
  constructor
  · linarith [hi.1]
  · linarith
end Formalism.LogVandermondeBounds.flipTwoThree
