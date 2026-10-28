-- Prove2me | solution 1 for D1Bound5.bennett_two_integral_summand_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:41.533292+00:00
-- url     : https://prove2.me/submissions/2b73d56c-1b4d-4ecf-a74a-f44ea8f2a5a4

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
import Theorems.Thm_D1Bound5_bennett_two_clear_column_one_signed
import Theorems.Thm_D1Bound5_bennett_two_taylor_scalar_mem

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



/-- The actual column-one residue summand is divisible by `a^k` inside
every subring containing the anchors. -/
theorem _root_.solution (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hb0 : b ≠ 0) (hab : a ≠ b)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d1) :
    ∃ q ∈ S,
      (((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h1) *
        Ring.choose (-((k + d0 : ℕ) : F)) h0 *
        Ring.choose (-((k + d2 : ℕ) : F)) h2) *
      ((a * b * (a - b) ^ 2) ^ k * (a * b * c + b) ^ (k - h1) *
        (b⁻¹) ^ (k + d0 + h0) * ((b - a)⁻¹) ^ (k + d2 + h2)) = a ^ k * q := by
  let t : F := ((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h1) *
    Ring.choose (-((k + d0 : ℕ) : F)) h0 *
    Ring.choose (-((k + d2 : ℕ) : F)) h2
  have ht : t ∈ S := bennett_two_taylor_scalar_mem S k h1 (k + d0) (k + d2) h0 h2
    (by omega)
  let u : F := (-1 : F) ^ (k + d2 + h2) *
    ((a * c + 1) ^ (k - h1) * b ^ (d2 + h2) * (a - b) ^ (k - (d2 + h2)))
  have hu : u ∈ S := S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _)
    (S.mul_mem (S.mul_mem (S.pow_mem (S.add_mem (S.mul_mem ha hc) S.one_mem) _)
      (S.pow_mem hb _)) (S.pow_mem (S.sub_mem ha hb) _))
  refine ⟨t * u, S.mul_mem ht hu, ?_⟩
  rw [bennett_two_clear_column_one_signed a b c hb0 hab k d0 d1 d2 h0 h1 h2 hk hd hh]
  dsimp [t, u]
  ring



end D1Bound5
end
