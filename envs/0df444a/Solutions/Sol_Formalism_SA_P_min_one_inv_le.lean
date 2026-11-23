-- Prove2me | solution 1 for Formalism.SA.P.min_one_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:27.193892+00:00
-- url     : https://prove2.me/submissions/50a8e604-dd9d-42bb-acb0-ad85bcfad7e8

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution (u : ℝ) (hu : 0 < u) : min 1 (1 / u) ≤ (1 / 2 : ℝ) ^ (Nat.log 2 ⌊u⌋₊) := by
  rcases lt_or_ge u 1 with h | h
  · rw [Nat.floor_eq_zero.mpr h, Nat.log_zero_right, pow_zero]
    exact min_le_left _ _
  · have hf : 0 < ⌊u⌋₊ := Nat.floor_pos.mpr h
    have h1 : 2 ^ Nat.log 2 ⌊u⌋₊ ≤ ⌊u⌋₊ := Nat.pow_log_le_self 2 hf.ne'
    have h2 : (2 : ℝ) ^ Nat.log 2 ⌊u⌋₊ ≤ u := by
      have h3 := Nat.floor_le hu.le
      have h1' : ((2 ^ Nat.log 2 ⌊u⌋₊ : ℕ) : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      linarith
    calc min 1 (1 / u) ≤ 1 / u := min_le_right _ _
      _ ≤ 1 / 2 ^ Nat.log 2 ⌊u⌋₊ := one_div_le_one_div_of_le (by positivity) h2
      _ = (1 / 2) ^ Nat.log 2 ⌊u⌋₊ := by rw [one_div_pow]
end Formalism.SA.P
