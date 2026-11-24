-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.root_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:37:44.587637+00:00
-- url     : https://prove2.me/submissions/de7a2d1e-09ec-43a8-8d76-e91684ce9482

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound

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
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (d : ℕ) (hd : 0 < d) (c : L) : (univ.filter (fun x : L => x ^ d = c)).card ≤ d := by
  calc _ ≤ (Polynomial.nthRoots d c).toFinset.card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp [Multiset.mem_toFinset, Polynomial.mem_nthRoots hd, hx]
    _ ≤ Multiset.card (Polynomial.nthRoots d c) := Multiset.toFinset_card_le _
    _ ≤ d := Polynomial.card_nthRoots d c
end Formalism.LogVandermondeBounds.StandardLattice
