-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:18:07.670825+00:00
-- url     : https://prove2.me/submissions/36abb12f-e3df-472f-85f0-2996becbe42d

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_coprime_two_pow

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
theorem _root_.solution (x : ℤ) (hx : Odd x) (K : ℕ) (hK : 1 ≤ K) :
    (2 : ℤ) ^ (K + 1) ∣ (x - 1) * (x + 1) ↔ (2 : ℤ) ^ K ∣ x - 1 ∨ (2 : ℤ) ^ K ∣ x + 1 := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨L, rfl⟩ : ∃ L, K = L + 1 := ⟨K - 1, by omega⟩
  have e1 : (2 * m + 1 - 1) * (2 * m + 1 + 1) = 4 * (m * (m + 1)) := by ring
  have e2 : (2 : ℤ) ^ (L + 1 + 1) = 4 * 2 ^ L := by ring
  have e3 : 2 * m + 1 - 1 = 2 * m := by ring
  have e4 : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
  have e5 : (2 : ℤ) ^ (L + 1) = 2 * 2 ^ L := by ring
  rw [e1, e2, e3, e4, e5, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  constructor
  · intro h
    rcases Int.even_or_odd m with hm | hm
    · exact Or.inl ((coprime_two_pow L hm.add_one).dvd_of_dvd_mul_right h)
    · exact Or.inr ((coprime_two_pow L hm).dvd_of_dvd_mul_left h)
  · rintro (h | h)
    · exact h.mul_right _
    · exact h.mul_left _
end Formalism.FrobeniusOrbits.Group
