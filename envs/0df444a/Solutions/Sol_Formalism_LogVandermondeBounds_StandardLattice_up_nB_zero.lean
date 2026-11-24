-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_nB_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:46.83397+00:00
-- url     : https://prove2.me/submissions/ecdf965b-564f-40ba-9af2-8380e7f085a4

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_sign_lo

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
theorem _root_.solution (n a c : ℕ) (hac : a < c) (hc : c < n + 1) : nBetween (n + 2) a c = 0 := by
  unfold nBetween
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  have hx' := Finset.mem_Ioo.mp hx
  rw [up_sign_lo n x (by omega), up_sign_lo n a (by omega)]
  exact fun h => h rfl
end Formalism.LogVandermondeBounds.StandardLattice
