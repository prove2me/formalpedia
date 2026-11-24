-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.coprime_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:00:11.190052+00:00
-- url     : https://prove2.me/submissions/fbcc7333-b558-48f8-b9d0-310e03937530

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
theorem _root_.solution (K : ℕ) {y : ℤ} (hy : Odd y) : IsCoprime ((2 : ℤ) ^ K) y := by
  obtain ⟨k, rfl⟩ := hy
  have h : IsCoprime (2 : ℤ) (2 * k + 1) := ⟨-k, 1, by ring⟩
  exact h.pow_left
end Formalism.FrobeniusOrbits.Group
