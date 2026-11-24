-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.order_le_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:32:20.920978+00:00
-- url     : https://prove2.me/submissions/eeb5465d-193b-404b-92a0-b9f7b897da0c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_card_H

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Group
namespace Formalism.FrobeniusOrbits.Group
theorem _root_.solution (e : ℕ) (x : HGrp e) : orderOf x ≤ 2 ^ e := by
  have h0 : orderOf x ∣ Nat.card (HGrp e) := by
    first
      | exact orderOf_dvd_natCard x
      | exact orderOf_dvd_card
  rw [card_H] at h0
  exact Nat.le_of_dvd (by positivity) h0
end Formalism.FrobeniusOrbits.Group
