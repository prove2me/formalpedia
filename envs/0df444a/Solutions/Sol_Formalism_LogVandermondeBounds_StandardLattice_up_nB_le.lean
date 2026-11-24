-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_nB_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:45.995213+00:00
-- url     : https://prove2.me/submissions/1c05122d-f188-45fa-9881-b7934cab6829

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
theorem _root_.solution (k a c : ℕ) : (nBetween k a c : ℝ) ≤ (c : ℝ) := by
  have h : nBetween k a c ≤ c := by
    unfold nBetween
    calc _ ≤ (Ioo a c).card := Finset.card_filter_le _ _
      _ = c - a - 1 := Nat.card_Ioo a c
      _ ≤ c := by omega
  exact_mod_cast h
end Formalism.LogVandermondeBounds.StandardLattice
