-- Prove2me | solution 1 for D1Bound5.bennett_two_taylor_scalar_mem
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:23.231495+00:00
-- url     : https://prove2.me/submissions/9f8913f6-b250-4ed4-9a1a-6d45478e57d4

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Theorems.Thm_D1Bound5_bennett_shifted_half_choose_uniform_is_integer

section
open Finset

namespace D1Bound5

/-!
The integer denominator bounds used in the Bennett residue construction.
The rational half-binomial identity is proved from the actual Catalan and
central-binomial identities in mathlib, then transported to every
characteristic-zero field. No coefficient-integrality premise is assumed.
-/





















/-- All generalized choose coefficients at an integer upper parameter are
integers, by functoriality of the actual binomial-ring structure on Z. -/
theorem bennett_integer_choose_eq_int
    {F : Type*} [Field F] [CharZero F] (z : ℤ) (h : ℕ) :
    Ring.choose (z : F) h = ((Ring.choose z h : ℤ) : F) := by
  exact (Ring.map_choose (Int.castRingHom F) z h).symm

/-- In particular, the reciprocal pole coefficients have integral binomial
factors for every natural pole order and every Taylor degree. -/
theorem bennett_negative_choose_is_integer
    {F : Type*} [Field F] [CharZero F] (k h : ℕ) :
    ∃ z : ℤ, Ring.choose (-(k : F)) h = (z : F) := by
  refine ⟨Ring.choose (-(k : ℤ)) h, ?_⟩
  simpa only [Int.cast_neg, Int.cast_natCast] using
    (bennett_integer_choose_eq_int (F := F) (-(k : ℤ)) h)

end D1Bound5
end

section
open Finset

namespace D1Bound5



/-- The three binomial factors in the two-node Taylor expansion are integral
after the uniform order-k power of four is included. Every integer is in S. -/
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F] (S : Subring F)
    (k h p q u v : ℕ) (hh : h ≤ k) :
    (((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h) *
      Ring.choose (-(p : F)) u * Ring.choose (-(q : F)) v) ∈ S := by
  obtain ⟨z, hz⟩ := bennett_shifted_half_choose_uniform_is_integer (F := F) k h k hh
  obtain ⟨zp, hp⟩ := bennett_negative_choose_is_integer (F := F) p u
  obtain ⟨zq, hq⟩ := bennett_negative_choose_is_integer (F := F) q v
  rw [hz, hp, hq]
  exact S.mul_mem (S.mul_mem (intCast_mem S z) (intCast_mem S zp)) (intCast_mem S zq)

end D1Bound5
end
