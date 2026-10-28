-- Prove2me | solution 1 for D1Bound5.bennett_shifted_half_choose_uniform_is_integer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:17:19.139799+00:00
-- url     : https://prove2.me/submissions/ceba8247-a50d-40a8-9747-e35449fb5fbd

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Definitions.Def_D1Bound5_BennettBinomialIntegrality_Definitions
import Theorems.Thm_D1Bound5_bennett_shifted_half_choose_scaled_eq_int_rat

section
open Finset

namespace D1Bound5

/-!
The integer denominator bounds used in the Bennett residue construction.
The rational half-binomial identity is proved from the actual Catalan and
central-binomial identities in mathlib, then transported to every
characteristic-zero field. No coefficient-integrality premise is assumed.
-/















/-- The denominator bound transported to an arbitrary characteristic-zero
field, with the integer numerator displayed explicitly. -/
theorem bennett_shifted_half_choose_scaled_eq_int
    {F : Type*} [Field F] [CharZero F] (k h : ℕ) :
    (4 : F) ^ h * Ring.choose ((k : F) + 1 / 2) h =
      (bennettScaledHalfShiftInt k h : F) := by
  have hmap := congrArg (algebraMap ℚ F)
    (bennett_shifted_half_choose_scaled_eq_int_rat k h)
  simpa only [map_mul, map_pow, Ring.map_choose, map_add, map_natCast,
    map_div₀, map_one, map_ofNat, map_intCast] using hmap



/-- A larger uniform power of four clears every coefficient below its
degree bound. This is the form used for a whole order-k residue row. -/
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F] (k h K : ℕ) (hh : h ≤ K) :
    ∃ z : ℤ, (4 : F) ^ K * Ring.choose ((k : F) + 1 / 2) h = (z : F) := by
  refine ⟨(4 : ℤ) ^ (K - h) * bennettScaledHalfShiftInt k h, ?_⟩
  calc
    (4 : F) ^ K * Ring.choose ((k : F) + 1 / 2) h =
        (4 : F) ^ ((K - h) + h) * Ring.choose ((k : F) + 1 / 2) h := by
      rw [Nat.sub_add_cancel hh]
    _ =
        (4 : F) ^ (K - h) *
          ((4 : F) ^ h * Ring.choose ((k : F) + 1 / 2) h) := by
      rw [pow_add]
      ring
    _ = _ := by rw [bennett_shifted_half_choose_scaled_eq_int]; push_cast; rfl





end D1Bound5
end
