-- Prove2me | solution 1 for Formalism.HC.Der.sq_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:49:07.264867+00:00
-- url     : https://prove2.me/submissions/d6561646-a932-4798-ac9b-1065a3da6b0a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC.Der
theorem _root_.solution {d : ℤ} (hd : d % 8 = 7) (k : ℕ) : ∃ s : ℤ, (2 : ℤ) ^ (k + 3) ∣ s ^ 2 + d := by
  induction k with
  | zero => exact ⟨1, by norm_num; omega⟩
  | succ k ih =>
    obtain ⟨s, t, ht⟩ := ih
    have e3 : (2 : ℤ) ^ (k + 3) = 8 * 2 ^ k := by ring
    rw [e3] at ht
    have hs1 : s % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one s with hs0 | hs1
      · exfalso
        obtain ⟨c, rfl⟩ : ∃ c, s = 2 * c := ⟨s / 2, by omega⟩
        have hd2 : d = 2 * (4 * 2 ^ k * t - 2 * c ^ 2) := by linear_combination ht
        have : d % 2 = 0 := by rw [hd2]; exact Int.mul_emod_right 2 _
        omega
      · exact hs1
    obtain ⟨a, rfl⟩ : ∃ a, s = 2 * a + 1 := ⟨s / 2, by omega⟩
    rcases Int.emod_two_eq_zero_or_one t with ht0 | ht1
    · obtain ⟨b, rfl⟩ : ∃ b, t = 2 * b := ⟨t / 2, by omega⟩
      refine ⟨2 * a + 1, b, ?_⟩
      have e4 : (2 : ℤ) ^ (k + 1 + 3) = 16 * 2 ^ k := by ring
      rw [e4]
      linear_combination ht
    · obtain ⟨b, rfl⟩ : ∃ b, t = 2 * b + 1 := ⟨t / 2, by omega⟩
      refine ⟨2 * a + 1 + 2 ^ (k + 2), a + b + 1 + 2 ^ k, ?_⟩
      have e2 : (2 : ℤ) ^ (k + 2) = 4 * 2 ^ k := by ring
      have e4 : (2 : ℤ) ^ (k + 1 + 3) = 16 * 2 ^ k := by ring
      rw [e2, e4]
      linear_combination ht
end Formalism.HC.Der
