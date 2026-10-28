-- Prove2me | solution 1 for D1Bound5.bennett_weighted_even_power_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:37.231907+00:00
-- url     : https://prove2.me/submissions/45799c9c-f5d0-4f7b-a1e6-7c1be74279f7

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
namespace D1Bound5

/-- Dividing a positive-order even power by its own anchor preserves
monotonicity. This is the scalar cancellation needed for the two columns. -/
theorem _root_.solution
    (A B H : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B)
    (hH : 0 ≤ H) (k : ℕ) (hk : 1 ≤ k) :
    (A^2*H)^k/A ≤ (B^2*H)^k/B := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hleft : (A^2*H)^(n+1)/A = A*(A^2*H)^n*H := by
    rw [pow_succ]
    field_simp [hA.ne']
    <;> ring
  have hright : (B^2*H)^(n+1)/B = B*(B^2*H)^n*H := by
    rw [pow_succ]
    field_simp [hB.ne']
    <;> ring
  rw [hleft, hright]
  gcongr



end D1Bound5
end
