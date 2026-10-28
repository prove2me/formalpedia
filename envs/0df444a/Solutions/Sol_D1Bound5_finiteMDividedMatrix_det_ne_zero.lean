-- Prove2me | solution 1 for D1Bound5.finiteMDividedMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:14.183271+00:00
-- url     : https://prove2.me/submissions/57f8f727-9d68-436f-8b3b-d99383a0bdac

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Theorems.Thm_D1Bound5_bennettClearedMatrix_det_half_eval_ne_zero
import Theorems.Thm_D1Bound5_finiteMNodes_injective
import Theorems.Thm_D1Bound5_finiteM_bennett_identity

section
open Finset Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]















/-- Nonsingularity of the actual integer polynomial matrix is inherited
from the proved arbitrary-order Bennett determinant. -/
theorem _root_.solution (a b s c : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) :
    (finiteMDividedMatrix a b s c).det ≠ 0 := by
  let nodes := finiteMNodes a b s
  let G := bennettClearedMatrix nodes 2 (1/2 : F)
  let ev := Polynomial.evalRingHom (a*b*s*c)
  let scale : F := (4*(a*b*s)^2*((a-b)*(a-s)*(b-s))^2)^2
  have hscale : scale ≠ 0 := by
    dsimp [scale]
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (mul_ne_zero (mul_ne_zero ha hb) hs)))
      (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab)
        (sub_ne_zero.mpr has)) (sub_ne_zero.mpr hbs))))
  have hG : G.det.eval (a*b*s*c) ≠ 0 :=
    bennettClearedMatrix_det_half_eval_ne_zero 3 nodes
      (finiteMNodes_injective a b s ha hb hs hab has hbs) 2 (by decide) rfl _
  have hev : (G.map ev).det ≠ 0 := by
    have hm := ev.map_det G
    change ev G.det = (G.map ev).det at hm
    rw [← hm]
    exact hG
  have hscaled : (scale • G.map ev).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hscale) hev
  have heq : scale • G.map ev =
      Matrix.diagonal (finiteMRowFactor a b s) * finiteMMatrix a b s c := by
    ext i j
    change finiteMBennettEntry a b s c i j = _
    rw [Matrix.diagonal_mul]
    exact finiteM_bennett_identity a b s c ha hb hs hab has hbs i j
  rw [heq, Matrix.det_mul, finiteMMatrix, Matrix.det_mul] at hscaled
  exact fun h => hscaled (by rw [h, zero_mul, mul_zero])

end D1Bound5
end
