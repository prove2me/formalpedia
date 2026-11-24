-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostRecip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:00:13.60089+00:00
-- url     : https://prove2.me/submissions/45675f6b-f10a-4f76-92e9-6709366b5f18

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
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostRecip := by
  unfold HostRecip
  intro q d h
  unfold HostHyp at h
  obtain ⟨-, -, hq8, hd16, hj⟩ := h
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hqo : Odd q := Nat.odd_iff.2 (by omega)
  have hdo : Odd d := Nat.odd_iff.2 (by omega)
  have hχq : ZMod.χ₄ (q : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four hq4
  have hχd : ZMod.χ₄ (d : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four hd4
  rw [jacobiSym.neg _ hqo, hχq] at hj
  rw [jacobiSym.neg _ hdo, hχd, jacobiSym.quadratic_reciprocity_three_mod_four hq4 hd4]
  linarith
end Formalism.FrobeniusOrbits
