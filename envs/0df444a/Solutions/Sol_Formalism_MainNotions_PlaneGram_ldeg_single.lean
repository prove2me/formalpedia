-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ldeg_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:42.722014+00:00
-- url     : https://prove2.me/submissions/2e9bc494-04e0-40b8-9b40-7502f88934e9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {L : Type} {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution [DecidableEq L] (i : L) (b : Fin r) (k : ℕ) (j : L) :
    ldeg (Finsupp.single (i, b) k) j = if j = i then k else 0 := by
  classical
  unfold ldeg
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hab
      rw [Finsupp.single_apply, if_neg]
      intro hh; exact hab (Prod.mk.inj hh).2.symm
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro hh; exact h (Prod.mk.inj hh).1.symm
end Formalism.MainNotions.PlaneGram
