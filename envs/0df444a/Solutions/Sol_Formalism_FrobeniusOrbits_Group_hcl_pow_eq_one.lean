-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.hcl_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:18.423959+00:00
-- url     : https://prove2.me/submissions/9f33e84b-b480-42a8-ac6b-7d849c3aa3b9

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
theorem _root_.solution (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) (k : ℕ) :
    (hcl e u) ^ k = 1 ↔ u ^ k = 1 ∨ u ^ k = -1 := by
  unfold hcl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    rcases Int.even_or_odd n with h | h
    · left
      rw [← hn, h.neg_one_zpow]
    · right
      rw [← hn, h.neg_one_zpow]
  · rintro (h | h)
    · exact ⟨0, by rw [zpow_zero, h]⟩
    · exact ⟨1, by rw [zpow_one, h]⟩
end Formalism.FrobeniusOrbits.Group
