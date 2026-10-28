-- Prove2me | solution 1 for D1Bound5.bennett_positive_weighted_coeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:24.936448+00:00
-- url     : https://prove2.me/submissions/63039d5c-553e-41f2-a3fa-5744cada7a8a

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
open Finset

namespace D1Bound5













/-- Finite weighted coefficient identity, separated from the analytic
summation proof so that each proof has its own bounded elaboration budget. -/
theorem _root_.solution
    (P Q : PowerSeries ℝ) (r : ℝ) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      (PowerSeries.coeff ij.1 P * r ^ ij.1) *
        (PowerSeries.coeff ij.2 Q * r ^ ij.2)) =
      PowerSeries.coeff n (P * Q) * r ^ n := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsumij := Finset.mem_antidiagonal.mp hij
  rw [← hsumij, pow_add]
  ring







end D1Bound5
end
