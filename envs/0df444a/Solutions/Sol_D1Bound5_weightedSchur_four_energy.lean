-- Prove2me | solution 1 for D1Bound5.weightedSchur_four_energy
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:23:55.696834+00:00
-- url     : https://prove2.me/submissions/208dbc2e-4176-4f61-a44b-c7c70720827e

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_weightedCS_four_row

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



end D1Bound5

namespace D1Bound5

/-- The four-dimensional real weighted Schur estimate, stated as a
squared-energy bound. The matrix entries need only be nonnegative and
symmetric, and the input vector may have arbitrary signs. -/
theorem _root_.solution
    (b : Matrix (Fin 4) (Fin 4) ℝ) (w x : Fin 4 → ℝ) (c : ℝ)
    (hb : ∀ i j, 0 ≤ b i j)
    (hw : ∀ i, 0 < w i) (hc : 0 ≤ c)
    (hsymm : ∀ i j, b i j = b j i)
    (hrows : ∀ i, (∑ j, b i j * w j) ≤ c * w i) :
    (∑ i, (∑ j, b i j * x j)^2) ≤ c^2 * (∑ j, (x j)^2) := by
  have hnon (i : Fin 4) : 0 ≤ ∑ j, b i j * (x j)^2 / w j :=
    Finset.sum_nonneg (fun j _ =>
      div_nonneg (mul_nonneg (hb i j) (sq_nonneg _)) (hw j).le)
  have hcol (j : Fin 4) : (∑ i, w i * b i j) ≤ c * w j := by
    calc
      (∑ i, w i * b i j) = ∑ i, b j i * w i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsymm i j]
        ring
      _ ≤ c * w j := hrows j
  have hrow (i : Fin 4) :
      (∑ j, b i j * x j)^2 ≤
        (c * w i) * (∑ j, b i j * (x j)^2 / w j) := by
    calc
      _ ≤ (∑ j, b i j * w j) * (∑ j, b i j * (x j)^2 / w j) :=
        weightedCS_four_row (b i) w x (hb i) hw
      _ ≤ (c * w i) * (∑ j, b i j * (x j)^2 / w j) :=
        mul_le_mul_of_nonneg_right (hrows i) (hnon i)
  calc
    (∑ i, (∑ j, b i j * x j)^2) ≤
        ∑ i, (c * w i) * (∑ j, b i j * (x j)^2 / w j) := by
          apply Finset.sum_le_sum
          intro i _
          exact hrow i
    _ = ∑ i, ∑ j, (x j)^2 / w j * (c * (w i * b i j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ j, ∑ i, (x j)^2 / w j * (c * (w i * b i j)) := Finset.sum_comm
    _ = ∑ j, ((x j)^2 / w j) * (c * (∑ i, w i * b i j)) := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [Finset.mul_sum]
    _ ≤ ∑ j, ((x j)^2 / w j) * (c * (c * w j)) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hcol j) hc)
            (div_nonneg (sq_nonneg _) (hw j).le)
    _ = c^2 * (∑ j, (x j)^2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          have hj : w j ≠ 0 := ne_of_gt (hw j)
          field_simp

end D1Bound5

namespace D1Bound5





end D1Bound5
end
