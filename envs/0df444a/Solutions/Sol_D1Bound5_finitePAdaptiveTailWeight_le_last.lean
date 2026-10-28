-- Prove2me | solution 1 for D1Bound5.finitePAdaptiveTailWeight_le_last
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:01.138391+00:00
-- url     : https://prove2.me/submissions/3b7bf1c0-b9b3-4953-bc8e-5c8b8a188b63

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveTailData_Definitions
import Theorems.Thm_D1Bound5_finitePAdaptiveTailWeight_eq

section
namespace D1Bound5





theorem _root_.solution (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (i : Fin 4) : finitePAdaptiveTailWeight i x ≤ finitePAdaptiveTailWeight 3 x := by
  have hp (n : ℕ) : x^(n+1) ≤ x^n := by
    simpa only [pow_succ,mul_one] using mul_le_mul_of_nonneg_left hx1 (pow_nonneg hx0 n)
  have h54 : x^5 ≤ x^4 := hp 4
  have h43 : x^4 ≤ x^3 := hp 3
  have h51 : x^5 ≤ x := by
    exact h54.trans (h43.trans ((hp 2).trans (by simpa only [pow_one] using hp 1)))
  rw [finitePAdaptiveTailWeight_eq,finitePAdaptiveTailWeight_eq]
  fin_cases i <;> norm_num [Matrix.cons_val_three]
  all_goals nlinarith only [h54,h43,h51,hx0,pow_nonneg hx0 2,pow_nonneg hx0 3,pow_nonneg hx0 4]









end D1Bound5
end
