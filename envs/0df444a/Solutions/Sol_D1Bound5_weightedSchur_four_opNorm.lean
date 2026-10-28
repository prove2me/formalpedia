-- Prove2me | solution 1 for D1Bound5.weightedSchur_four_opNorm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:34:28.630726+00:00
-- url     : https://prove2.me/submissions/9be55d1f-b7a0-4e00-913c-c3014bf07eea

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
import Theorems.Thm_D1Bound5_weightedSchur_four_energy

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5

/-- A nonnegative symmetric entrywise envelope with positive weighted
row sums bounds the complex Euclidean L2 operator norm. The complex
matrix itself need not be symmetric or Hermitian. -/
theorem _root_.solution
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (b : Matrix (Fin 4) (Fin 4) ℝ) (w : Fin 4 → ℝ) (c : ℝ)
    (hb : ∀ i j, 0 ≤ b i j)
    (hw : ∀ i, 0 < w i) (hc : 0 ≤ c)
    (hsymm : ∀ i j, b i j = b j i)
    (hrows : ∀ i, (∑ j, b i j * w j) ≤ c * w i)
    (hEb : ∀ i j, ‖E i j‖ ≤ b i j) :
    ‖E‖ ≤ c := by
  let T : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
    Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℂ) E
  change ‖T‖ ≤ c
  refine T.opNorm_le_bound hc (fun y => ?_)
  have hsum (i : Fin 4) :
      ‖(E *ᵥ WithLp.ofLp y) i‖ ≤
        ∑ j, b i j * ‖WithLp.ofLp y j‖ := by
    rw [Matrix.mulVec, dotProduct]
    calc
      ‖∑ j, E i j * WithLp.ofLp y j‖ ≤
          ∑ j, ‖E i j * WithLp.ofLp y j‖ := norm_sum_le _ _
      _ = ∑ j, ‖E i j‖ * ‖WithLp.ofLp y j‖ := by simp_rw [norm_mul]
      _ ≤ ∑ j, b i j * ‖WithLp.ofLp y j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hEb i j) (norm_nonneg _)
  have hsumpos (i : Fin 4) :
      0 ≤ ∑ j, b i j * ‖WithLp.ofLp y j‖ :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hb i j) (norm_nonneg _))
  have hsquares (i : Fin 4) :
      ‖(E *ᵥ WithLp.ofLp y) i‖^2 ≤
        (∑ j, b i j * ‖WithLp.ofLp y j‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (hsumpos i)).mpr (hsum i)
  have henergy := weightedSchur_four_energy b w
      (fun j => ‖WithLp.ofLp y j‖) c hb hw hc hsymm hrows
  have hbound : ‖T y‖^2 ≤ c^2 * ‖y‖^2 := by
    calc
      ‖T y‖^2 =
          ∑ i, ‖(E *ᵥ WithLp.ofLp y) i‖^2 := by
            rw [EuclideanSpace.norm_sq_eq]
            simp only [T, Matrix.ofLp_toEuclideanCLM]
      _ ≤ ∑ i, (∑ j, b i j * ‖WithLp.ofLp y j‖)^2 := by
            exact Finset.sum_le_sum (fun i _ => hsquares i)
      _ ≤ c^2 * (∑ j, ‖WithLp.ofLp y j‖^2) := henergy
      _ = c^2 * ‖y‖^2 := by rw [EuclideanSpace.norm_sq_eq]
  have hbound' : ‖T y‖^2 ≤ (c * ‖y‖)^2 := by
    nlinarith only [hbound]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg y))).mp hbound'



end D1Bound5
end
