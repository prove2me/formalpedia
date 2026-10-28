-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_row_lift
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:40:04.723961+00:00
-- url     : https://prove2.me/submissions/c12d608c-bab7-4c19-bca0-e54c316fa8aa

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_one_integral_divisible
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_two_integral_divisible
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_zero_integral

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



























/-- Every actual two-anchor row lifts to the original ring, with the exact
column powers retained. Instantiating R with the full ring of integers gives
the arithmetic integrality/divisibility bridge without unique factorization. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* F) (a b c : R)
    (ha0 : f a ≠ 0) (hb0 : f b ≠ 0) (hab : f a ≠ f b)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ∃ q0 q1 q2 : R,
      f q0 = bennettTwoClearedEntry (f a) (f b) (f c) k i 0 ∧
      f (a ^ k * q1) = bennettTwoClearedEntry (f a) (f b) (f c) k i 1 ∧
      f (b ^ k * q2) = bennettTwoClearedEntry (f a) (f b) (f c) k i 2 := by
  have ha : f a ∈ f.range := ⟨a, rfl⟩
  have hb : f b ∈ f.range := ⟨b, rfl⟩
  have hc : f c ∈ f.range := ⟨c, rfl⟩
  obtain ⟨u0, hu0, he0⟩ := bennettTwoClearedEntry_zero_integral f.range
    (f a) (f b) (f c) ha hb hc ha0 hb0 k hk i
  obtain ⟨u1, hu1, he1⟩ := bennettTwoClearedEntry_one_integral_divisible f.range
    (f a) (f b) (f c) ha hb hc hb0 hab k hk i
  obtain ⟨u2, hu2, he2⟩ := bennettTwoClearedEntry_two_integral_divisible f.range
    (f a) (f b) (f c) ha hb hc ha0 hab k hk i
  obtain ⟨q0, hq0⟩ := hu0
  obtain ⟨q1, hq1⟩ := hu1
  obtain ⟨q2, hq2⟩ := hu2
  refine ⟨q0, q1, q2, ?_, ?_, ?_⟩
  · rw [hq0, he0, one_mul]
  · rw [map_mul, map_pow, hq1, he1]
  · rw [map_mul, map_pow, hq2, he2]

end D1Bound5
end
