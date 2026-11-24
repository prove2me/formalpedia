-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.sep_other_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:30.934528+00:00
-- url     : https://prove2.me/submissions/74a1e015-6991-4ddd-a81d-667755aa4896

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation
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
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu nu' : Fin n → ℤ}
    (h' : Interlace lam nu') (hb : B0 lam nu' = B0 lam nu) (hne : nu' ≠ nu) :
    sep lam nu nu' = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  unfold sep
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (i := nu' i) (Finset.mem_erase.mpr ⟨hi, mem_Iset_of h' hb i⟩)
  unfold ev
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring
end Formalism.LogVandermondeBounds.flipTwoThree
