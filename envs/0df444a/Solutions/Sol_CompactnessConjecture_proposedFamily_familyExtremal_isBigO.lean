-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_familyExtremal_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/947577b7-550b-4fae-a297-c2d70bbff108

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_familyExtremal_sixteenth_power_le

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (familyExtremal proposedFamily n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((21 : ℝ) / 16)) := by
  let C : ℝ := max compactnessHostPowerConstant 1
  have hCone : 1 ≤ C := le_max_right _ _
  have hCnonneg : 0 ≤ C := zero_le_one.trans hCone
  have hconstant : compactnessHostPowerConstant ≤ C ^ (16 : ℕ) :=
    (le_max_left _ _).trans (le_self_pow₀ hCone (by norm_num))
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, Filter.Eventually.of_forall fun n => ?_⟩
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hscale :
      ((n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) =
        (n : ℝ) ^ (21 : ℕ) := by
    rw [← Real.rpow_mul_natCast hnnonneg ((21 : ℝ) / 16) 16]
    norm_num
  have hpower :
      (familyExtremal proposedFamily n : ℝ) ^ (16 : ℕ) ≤
        (C * (n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) := by
    calc
      (familyExtremal proposedFamily n : ℝ) ^ (16 : ℕ) ≤
          compactnessHostPowerConstant * (n : ℝ) ^ (21 : ℕ) :=
        proposedFamily_familyExtremal_sixteenth_power_le n
      _ ≤ C ^ (16 : ℕ) * (n : ℝ) ^ (21 : ℕ) :=
        mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = (C * (n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) := by
        rw [mul_pow, hscale]
  have hbound := le_of_pow_le_pow_left₀
    (by norm_num : (16 : ℕ) ≠ 0)
    (mul_nonneg hCnonneg (Real.rpow_nonneg hnnonneg _)) hpower
  have hextremal_nonneg :
      (0 : ℝ) ≤ (familyExtremal proposedFamily n : ℝ) :=
    Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hextremal_nonneg,
    abs_of_nonneg (Real.rpow_nonneg hnnonneg _)] using hbound
end CompactnessConjecture
