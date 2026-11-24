-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.cast_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:56:09.110856+00:00
-- url     : https://prove2.me/submissions/a453e792-4c16-48c2-a7d7-a889217e857d

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
theorem _root_.solution (m : ℕ) (z : ℤ) : (z : ZMod m) = -1 ↔ (m : ℤ) ∣ z + 1 := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub (-1) z m
  rw [Int.cast_neg, Int.cast_one, sub_neg_eq_add] at h
  rw [← h]
  exact eq_comm
end Formalism.FrobeniusOrbits.Group
