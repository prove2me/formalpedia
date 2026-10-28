-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:22.193662+00:00
-- url     : https://prove2.me/submissions/178e7811-1e22-4970-b59d-cefc83547e8f

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

noncomputable section
section InverseMatrixCancellation
open scoped BigOperators
/-- Finite inverse-Hessian cancellation for the weak Letwin (2.2) test.
All analytic data are replaced by arbitrary finite matrices and coordinate vectors. -/
 theorem solution {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hdet : IsUnit A.det)
    (a : ℝ) (b p q r : Fin n → ℝ) :
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
      (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
      (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
        a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by
  have hsymm (i j : Fin n) : A⁻¹ i j = A⁻¹ j i := by
    simpa only [star_trivial] using hA.inv.apply j i
  have hcancel (i : Fin n) :
      (∑ j, A⁻¹ i j * (∑ k, A j k * q k)) = q i := by
    calc
      (∑ j, A⁻¹ i j * (∑ k, A j k * q k)) =
          ∑ k, (∑ j, A⁻¹ i j * A j k) * q k := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = q i := by
        simp only [← Matrix.mul_apply, Matrix.nonsing_inv_mul A hdet]
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        simp
  have henergy :
      (∑ i, ∑ j, A⁻¹ i j * b j * r i) =
        ∑ i, ∑ j, A⁻¹ i j * b i * r j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have htrace :
      (A⁻¹ * B).trace = ∑ i, ∑ j, A⁻¹ i j * B j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  calc
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
        (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
        ∑ i, ∑ j,
          (A⁻¹ i j * b j * r i + a * (A⁻¹ i j * B j i) -
            a * (A⁻¹ i j * (∑ k, A j k * q k) * r i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, A⁻¹ i j * b j * r i) +
          a * (∑ i, ∑ j, A⁻¹ i j * B j i) -
          a * (∑ i, q i * r i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hcancel]
    _ = (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
          a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by
      rw [henergy, ← htrace]
      ring
