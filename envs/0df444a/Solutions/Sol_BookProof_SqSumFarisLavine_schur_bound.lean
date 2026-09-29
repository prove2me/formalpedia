-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.schur_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T17:54:52.900251+00:00
-- url     : https://prove2.me/submissions/3d9607dc-ef4b-4e21-ac17-71b392cc67dd

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.schur_bound
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℝ) {a b : ℝ}
    (ha0 : 0 ≤ a)
    (ha : ∀ i, ∑ j : J, |A i j| ≤ a) (hb : ∀ j, ∑ i : I, |A i j| ≤ b) (y : J → ℝ) :
    ∑ i : I, (∑ j : J, A i j * y j) ^ 2 ≤ a * b * ∑ j : J, (y j) ^ 2 := by

  have hrow : ∀ i : I, (∑ j : J, A i j * y j) ^ 2 ≤ a * ∑ j : J, |A i j| * (y j) ^ 2 := by
    intro i
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J)
      (fun j => Real.sqrt |A i j|) (fun j => Real.sqrt |A i j| * |y j|)
    have h1 : ∑ j : J, Real.sqrt |A i j| * (Real.sqrt |A i j| * |y j|)
        = ∑ j : J, |A i j| * |y j| := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg (A i j))]
    have h2 : ∑ j : J, (Real.sqrt |A i j|) ^ 2 = ∑ j : J, |A i j| :=
      Finset.sum_congr rfl fun j _ => Real.sq_sqrt (abs_nonneg _)
    have h3 : ∑ j : J, (Real.sqrt |A i j| * |y j|) ^ 2 = ∑ j : J, |A i j| * (y j) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    rw [h1, h2, h3] at hcs
    have habs : |∑ j : J, A i j * y j| ≤ ∑ j : J, |A i j| * |y j| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    have hnn : 0 ≤ ∑ j : J, |A i j| * |y j| :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsq : (∑ j : J, A i j * y j) ^ 2 ≤ (∑ j : J, |A i j| * |y j|) ^ 2 := by
      rw [← sq_abs (∑ j : J, A i j * y j)]
      nlinarith [abs_nonneg (∑ j : J, A i j * y j)]
    have hpos : 0 ≤ ∑ j : J, |A i j| * (y j) ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    calc (∑ j : J, A i j * y j) ^ 2 ≤ (∑ j : J, |A i j| * |y j|) ^ 2 := hsq
      _ ≤ (∑ j : J, |A i j|) * ∑ j : J, |A i j| * (y j) ^ 2 := hcs
      _ ≤ a * ∑ j : J, |A i j| * (y j) ^ 2 :=
          mul_le_mul_of_nonneg_right (ha i) hpos
  calc ∑ i : I, (∑ j : J, A i j * y j) ^ 2
      ≤ ∑ i : I, a * ∑ j : J, |A i j| * (y j) ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = a * ∑ j : J, (∑ i : I, |A i j|) * (y j) ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    _ ≤ a * ∑ j : J, b * (y j) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) ha0
        exact mul_le_mul_of_nonneg_right (hb j) (sq_nonneg _)
    _ = a * b * ∑ j : J, (y j) ^ 2 := by rw [← Finset.mul_sum, mul_assoc]
