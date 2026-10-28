-- Prove2me | solution 1 for D1Bound5.bennett_two_integral_summand_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:10.904027+00:00
-- url     : https://prove2.me/submissions/a04ce6b8-6a06-4d53-b0a9-69533bd991c1

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_two_clear_column_zero_signed
import Theorems.Thm_D1Bound5_bennett_two_taylor_scalar_mem

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- The actual column-zero residue summand, with all binomial factors and
pole signs, is integral in every subring containing the anchor entries. -/
theorem _root_.solution (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d0) :
    ∃ q ∈ S,
      (((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h0) *
        Ring.choose (-((k + d1 : ℕ) : F)) h1 *
        Ring.choose (-((k + d2 : ℕ) : F)) h2) *
      ((a * b * (a - b) ^ 2) ^ k * (a * b * c) ^ (k - h0) *
        ((-b)⁻¹) ^ (k + d1 + h1) * ((-a)⁻¹) ^ (k + d2 + h2)) = 1 * q := by
  let t : F := ((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h0) *
    Ring.choose (-((k + d1 : ℕ) : F)) h1 *
    Ring.choose (-((k + d2 : ℕ) : F)) h2
  have ht : t ∈ S := bennett_two_taylor_scalar_mem S k h0 (k + d1) (k + d2) h1 h2
    (by omega)
  let u : F := (-1 : F) ^ ((k + d1 + h1) + (k + d2 + h2)) *
    (a ^ (d1 + h1) * b ^ (d2 + h2) * c ^ (k - h0) * (a - b) ^ (2 * k))
  have hu : u ∈ S := S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _)
    (S.mul_mem (S.mul_mem (S.mul_mem (S.pow_mem ha _) (S.pow_mem hb _))
      (S.pow_mem hc _)) (S.pow_mem (S.sub_mem ha hb) _))
  refine ⟨t * u, S.mul_mem ht hu, ?_⟩
  rw [bennett_two_clear_column_zero_signed a b c ha0 hb0 k d0 d1 d2 h0 h1 h2 hk hd hh]
  change t * u = 1 * (t * u)
  rw [one_mul]





end D1Bound5
end
