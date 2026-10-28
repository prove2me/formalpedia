-- Prove2me | solution 1 for D1Bound5.finiteA_choose_four
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:36:37.781283+00:00
-- url     : https://prove2.me/submissions/166e4fc2-23bf-4aed-85ee-c1abaeffc458

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_finiteA_choose_three

section
namespace D1Bound5
variable {F : Type*} [Field F] [CharZero F]





theorem _root_.solution (r : F) : Ring.choose r 4 = r*(r-1)*(r-2)*(r-3)/24 := by
  have h := Ring.choose_smul_choose (r := r) (n := 4) (k := 1) (by decide)
  norm_num [nsmul_eq_mul,Ring.choose_one_right,finiteA_choose_three] at h
  apply (eq_div_iff (by norm_num : (24 : F) ≠ 0)).mpr
  linear_combination 6*h



end D1Bound5
end
