-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.not_four_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:12.944073+00:00
-- url     : https://prove2.me/submissions/6bacb7cb-1d9c-4a1b-a657-ff110c55d00f

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
theorem _root_.solution (x : ℤ) (hx : Odd x) : ¬ (4 : ℤ) ∣ x ^ 2 + 1 := by
  obtain ⟨m, rfl⟩ := hx
  rintro ⟨c, hc⟩
  have e : (2 * m + 1) ^ 2 + 1 = 4 * (m ^ 2 + m) + 2 := by ring
  rw [e] at hc
  generalize m ^ 2 + m = s at hc
  omega
end Formalism.FrobeniusOrbits.Group
