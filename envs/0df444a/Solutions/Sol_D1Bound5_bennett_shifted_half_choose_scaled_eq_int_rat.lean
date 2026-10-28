-- Prove2me | solution 1 for D1Bound5.bennett_shifted_half_choose_scaled_eq_int_rat
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:17:20.096086+00:00
-- url     : https://prove2.me/submissions/e913fe1b-014c-4efc-be70-5111c910421b

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Definitions.Def_D1Bound5_BennettBinomialIntegrality_Definitions
import Theorems.Thm_D1Bound5_bennett_half_choose_scaled_catalan

section
open Finset

namespace D1Bound5

/-!
The integer denominator bounds used in the Bennett residue construction.
The rational half-binomial identity is proved from the actual Catalan and
central-binomial identities in mathlib, then transported to every
characteristic-zero field. No coefficient-integrality premise is assumed.
-/









theorem bennett_half_choose_scaled_eq_int (h : ℕ) :
    (4 : ℚ) ^ h * Ring.choose (1 / 2 : ℚ) h = (bennettScaledHalfInt h : ℚ) := by
  cases h with
  | zero => simp [bennettScaledHalfInt]
  | succ n =>
      rw [bennett_half_choose_scaled_catalan]
      simp [bennettScaledHalfInt]



theorem _root_.solution (k h : ℕ) :
    (4 : ℚ) ^ h * Ring.choose ((k : ℚ) + 1 / 2) h =
      (bennettScaledHalfShiftInt k h : ℚ) := by
  rw [Ring.add_choose_eq h (Commute.all _ _), Finset.mul_sum]
  unfold bennettScaledHalfShiftInt
  push_cast
  apply Finset.sum_congr rfl
  intro uv huv
  have he : uv.1 + uv.2 = h := Finset.mem_antidiagonal.mp huv
  rw [← he, pow_add, Ring.choose_natCast]
  calc
    ((4 : ℚ) ^ uv.1 * 4 ^ uv.2) *
        ((k.choose uv.1 : ℚ) * Ring.choose (1 / 2 : ℚ) uv.2) =
        ((4 : ℚ) ^ uv.1 * (k.choose uv.1 : ℚ)) *
          (4 ^ uv.2 * Ring.choose (1 / 2 : ℚ) uv.2) := by ring
    _ = _ := by rw [bennett_half_choose_scaled_eq_int]











end D1Bound5
end
