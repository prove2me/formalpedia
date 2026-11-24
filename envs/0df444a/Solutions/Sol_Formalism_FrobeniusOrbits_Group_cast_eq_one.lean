-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.cast_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:20.115349+00:00
-- url     : https://prove2.me/submissions/636305b5-5f2c-45a2-a3ee-e87c7203101b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow

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
theorem _root_.solution (m : ℕ) (z : ℤ) : (z : ZMod m) = 1 ↔ (m : ℤ) ∣ z - 1 := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub 1 z m
  rw [Int.cast_one] at h
  rw [← h]
  exact eq_comm
end Formalism.FrobeniusOrbits.Group
