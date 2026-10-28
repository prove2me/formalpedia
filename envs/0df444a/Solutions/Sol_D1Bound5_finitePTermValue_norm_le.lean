-- Prove2me | solution 1 for D1Bound5.finitePTermValue_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:33.228318+00:00
-- url     : https://prove2.me/submissions/69d9622f-cab9-48f2-99c9-2818314d259f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Theorems.Thm_D1Bound5_finiteP_monomial_le

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three













/-- Every actual monomial lies in one of the two height boxes. -/
theorem finitePRootTerms_exponents (i : Fin 4) (l j t : Fin 3) :
    let u := finitePRootTerms i l j t
    (u.2.1+u.2.2.1+u.2.2.2 ≤ 5 ∧ u.2.2.2 ≤ 2) ∨
      (u.2.1+u.2.2.1 ≤ 1 ∧ u.2.2.2 ≤ 3) := by
  fin_cases i <;> fin_cases l <;> fin_cases j <;> fin_cases t <;>
    norm_num [finitePRootTerms]



theorem _root_.solution (a b s : ℂ) (hA : 1 ≤ ‖a‖)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (i : Fin 4) (l j t : Fin 3) :
    ‖finitePTermValue (finitePRootTerms i l j t) a b s‖ ≤
      |((finitePRootTerms i l j t).1 : ℝ)| *
        max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2) := by
  let u := finitePRootTerms i l j t
  have hm := finiteP_monomial_le ‖a‖ ‖b‖ ‖s‖ hA hAB hBS
    u.2.1 u.2.2.1 u.2.2.2 (finitePRootTerms_exponents i l j t)
  have hnorm : ‖(u.1 : ℂ)‖ = |(u.1 : ℝ)| := by simp
  simpa [finitePTermValue, norm_mul, norm_pow, hnorm, mul_assoc, u] using
      mul_le_mul_of_nonneg_left hm (abs_nonneg (u.1 : ℝ))











end D1Bound5
end
