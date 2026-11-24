-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.card_erase_Iset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:28.872212+00:00
-- url     : https://prove2.me/submissions/80f64cd0-ea20-4278-8524-00bda866f78f

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_loss_bound_nonneg
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_len_nonneg
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_mem_Iset_of

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
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) :
    ((Iset lam (B0 lam nu) i).erase (nu i)).card = (min (len lam i) (B0 lam nu)).toNat := by
  rw [Finset.card_erase_of_mem (mem_Iset_of h rfl i)]
  unfold Iset
  rw [Int.card_Icc]
  have h0 : 0 ≤ min (len lam i) (B0 lam nu) := le_min (len_nonneg h i) (loss_bound_nonneg h)
  omega
end Formalism.LogVandermondeBounds.flipTwoThree
