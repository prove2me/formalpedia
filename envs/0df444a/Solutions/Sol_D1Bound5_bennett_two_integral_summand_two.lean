-- Prove2me | solution 1 for D1Bound5.bennett_two_integral_summand_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:08.487375+00:00
-- url     : https://prove2.me/submissions/1a8b83d6-d15a-4c40-8898-7f281adb6fbc

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
import Theorems.Thm_D1Bound5_bennett_two_clear_column_two
import Theorems.Thm_D1Bound5_bennett_two_taylor_scalar_mem

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





/-- The actual column-two residue summand is divisible by `b^k` inside
every subring containing the anchors. -/
theorem _root_.solution (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha0 : a ≠ 0) (hab : a ≠ b)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d2) :
    ∃ q ∈ S,
      (((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h2) *
        Ring.choose (-((k + d0 : ℕ) : F)) h0 *
        Ring.choose (-((k + d1 : ℕ) : F)) h1) *
      ((a * b * (a - b) ^ 2) ^ k * (a * b * c + a) ^ (k - h2) *
        (a⁻¹) ^ (k + d0 + h0) * ((a - b)⁻¹) ^ (k + d1 + h1)) = b ^ k * q := by
  let t : F := ((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h2) *
    Ring.choose (-((k + d0 : ℕ) : F)) h0 *
    Ring.choose (-((k + d1 : ℕ) : F)) h1
  have ht : t ∈ S := bennett_two_taylor_scalar_mem S k h2 (k + d0) (k + d1) h0 h1
    (by omega)
  let u : F := (b * c + 1) ^ (k - h2) * a ^ (d1 + h1) *
    (a - b) ^ (k - (d1 + h1))
  have hu : u ∈ S := S.mul_mem
    (S.mul_mem (S.pow_mem (S.add_mem (S.mul_mem hb hc) S.one_mem) _) (S.pow_mem ha _))
    (S.pow_mem (S.sub_mem ha hb) _)
  refine ⟨t * u, S.mul_mem ht hu, ?_⟩
  rw [bennett_two_clear_column_two a b c ha0 hab k d0 d1 d2 h0 h1 h2 hk hd hh]
  dsimp [t, u]
  ring

end D1Bound5
end
