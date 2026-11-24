-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.interlacing_separation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:56.528802+00:00
-- url     : https://prove2.me/submissions/245c641a-a434-4f9d-845e-126e3f8d4841

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_mem_Iset_of
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_Iset_disj
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_sep_self_ne_zero
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_sep_self_abs
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_sep_other_zero

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
theorem _root_.solution : InterlacingSeparation := by
  intro n lam nu h
  exact ⟨fun nu' h' hb i => mem_Iset_of h' hb i,
    fun i j hij => Iset_disj h.1 _ i j hij,
    sep_self_ne_zero h,
    sep_self_abs h,
    fun nu' h' hb hne => sep_other_zero h' hb hne⟩
end Formalism.LogVandermondeBounds.flipTwoThree
