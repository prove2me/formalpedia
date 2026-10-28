-- Prove2me | solution 1 for D1Bound5.finiteN3_choose_three
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:32.424985+00:00
-- url     : https://prove2.me/submissions/6a3b1ce2-3c60-41d7-b9cd-79dcde687968

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_finiteN3_choose_two

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



theorem _root_.solution (r : F) : Ring.choose r 3 = r*(r-1)*(r-2)/6 := by
  have h := Ring.choose_smul_choose (r := r) (n := 3) (k := 1) (by decide)
  norm_num [nsmul_eq_mul, Ring.choose_one_right, finiteN3_choose_two] at h
  apply (eq_div_iff (by norm_num : (6 : F) ≠ 0)).mpr
  linear_combination 2*h



end D1Bound5
end
