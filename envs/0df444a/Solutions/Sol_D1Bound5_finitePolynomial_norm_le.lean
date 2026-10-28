-- Prove2me | solution 1 for D1Bound5.finitePolynomial_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:06.134237+00:00
-- url     : https://prove2.me/submissions/dc462112-2568-4651-9181-795f40ca1cfc

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

theorem _root_.solution (k : ℕ) (a : Fin (k+1) → ℂ) (c : ℂ) :
    ‖∑ ell, a ell*c^(ell : ℕ)‖ ≤ ∑ ell, ‖a ell‖*‖c‖^(ell : ℕ) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ell hell
  rw [norm_mul,norm_pow]







end D1Bound5
end
