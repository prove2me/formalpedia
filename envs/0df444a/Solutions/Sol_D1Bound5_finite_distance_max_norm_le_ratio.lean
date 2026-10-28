-- Prove2me | solution 1 for D1Bound5.finite_distance_max_norm_le_ratio
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:21.447925+00:00
-- url     : https://prove2.me/submissions/7d1fe40a-e422-4ef9-9185-537100216490

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- Exact distance envelope valid even when the two anchors are close.
The second maximum term handles the row whose cleared divisor is the
anchor rather than the anchor difference. -/
theorem _root_.solution (x y : ℂ) (r : ℝ) (n : ℕ)
    (hr : 0 ≤ r) (hn : 1 ≤ n) (hxy : ‖x‖ ≤ r*‖y‖) :
    max (‖x-y‖^n) (‖x‖*‖x-y‖^(n-1)) ≤ (1+r)^n*‖y‖^n := by
  have hbound : ‖x-y‖ ≤ (1+r)*‖y‖ := by
    have hh := norm_sub_le x y
    nlinarith only [hh,hxy]
  have hx : ‖x‖ ≤ (1+r)*‖y‖ := by nlinarith only [hxy,norm_nonneg y]
  have hbase : 0 ≤ (1+r)*‖y‖ := by positivity
  have hsum : 1+(n-1)=n := by omega
  apply max_le
  · simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (x-y)) hbound n
  · calc
      ‖x‖*‖x-y‖^(n-1) ≤ ((1+r)*‖y‖)*((1+r)*‖y‖)^(n-1) := by gcongr
      _ = ((1+r)*‖y‖)^n := by rw [← pow_succ']; congr 1; omega
      _ = (1+r)^n*‖y‖^n := mul_pow _ _ _



end D1Bound5
end
