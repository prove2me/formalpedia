-- Prove2me | solution 1 for BLTCounting.AccuracySpace.claim_6_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:57:13.074794+00:00
-- url     : https://prove2.me/submissions/c35481d3-9c33-43e9-833b-4b4e5925a58b

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms

open Matrix BLTCounting.AccuracySpace

namespace AuxClaim61

lemma le_maxColSum {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℂ) (j : n) :
    ∑ i : m, ‖B i j‖ ≤ maxColSum B :=
  le_ciSup (f := fun j' : n => ∑ i : m, ‖B i j'‖) (Finite.bddAbove_range _) j

lemma le_maxRowSum {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℂ) (i : m) :
    ∑ j : n, ‖B i j‖ ≤ maxRowSum B :=
  le_ciSup (f := fun i' : m => ∑ j : n, ‖B i' j‖) (Finite.bddAbove_range _) i

lemma maxColSum_nonneg {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℂ) :
    0 ≤ maxColSum B := by
  rcases isEmpty_or_nonempty n with _ | ⟨⟨j₀⟩⟩
  · simp [maxColSum]
  · exact le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) (le_maxColSum B j₀)

lemma maxRowSum_nonneg {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℂ) :
    0 ≤ maxRowSum B := by
  rcases isEmpty_or_nonempty m with _ | ⟨⟨i₀⟩⟩
  · simp [maxRowSum]
  · exact le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) (le_maxRowSum B i₀)

lemma row_bound {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℂ)
    (x : n → ℂ) (i : m) :
    ‖(B *ᵥ x) i‖ ^ 2 ≤ maxRowSum B * ∑ j : n, ‖B i j‖ * ‖x j‖ ^ 2 := by
  have h1 : ‖(B *ᵥ x) i‖ ≤ ∑ j : n, ‖B i j‖ * ‖x j‖ := by
    simpa [Matrix.mulVec, dotProduct, norm_mul] using
      norm_sum_le Finset.univ (fun j : n => B i j * x j)
  have h2 : (∑ j : n, ‖B i j‖ * ‖x j‖) ^ 2 ≤
      (∑ j : n, ‖B i j‖) * ∑ j : n, ‖B i j‖ * ‖x j‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n)
      (fun j => Real.sqrt ‖B i j‖) (fun j => Real.sqrt ‖B i j‖ * ‖x j‖)
    have hrew1 : (∑ j : n, Real.sqrt ‖B i j‖ * (Real.sqrt ‖B i j‖ * ‖x j‖)) =
        ∑ j : n, ‖B i j‖ * ‖x j‖ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have hrew2 : (∑ j : n, Real.sqrt ‖B i j‖ ^ 2) = ∑ j : n, ‖B i j‖ := by
      refine Finset.sum_congr rfl fun j _ => Real.sq_sqrt (norm_nonneg _)
    have hrew3 : (∑ j : n, (Real.sqrt ‖B i j‖ * ‖x j‖) ^ 2) =
        ∑ j : n, ‖B i j‖ * ‖x j‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    rw [hrew1, hrew2, hrew3] at hcs
    exact hcs
  have hsq : ‖(B *ᵥ x) i‖ ^ 2 ≤ (∑ j : n, ‖B i j‖ * ‖x j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine le_trans hsq (le_trans h2 ?_)
  exact mul_le_mul_of_nonneg_right (le_maxRowSum B i)
    (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

end AuxClaim61

theorem solution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (B : Matrix m n ℂ) :
    specNorm B ^ 2 ≤ maxColSum B * maxRowSum B := by
  have hprod : 0 ≤ maxColSum B * maxRowSum B :=
    mul_nonneg (AuxClaim61.maxColSum_nonneg B) (AuxClaim61.maxRowSum_nonneg B)
  have hop : specNorm B ≤ Real.sqrt (maxColSum B * maxRowSum B) := by
    unfold specNorm
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
      fun (x : EuclideanSpace ℂ n) => ?_
    have h_lhs : ‖(Matrix.toEuclideanLin B).toContinuousLinearMap x‖ ^ 2 =
        ∑ i : m, ‖(B *ᵥ x.ofLp) i‖ ^ 2 := by
      change ‖Matrix.toEuclideanLin B x‖ ^ 2 = ∑ i : m, ‖(B *ᵥ x.ofLp) i‖ ^ 2
      rw [PiLp.norm_sq_eq_of_L2, Matrix.toLpLin_apply]
    have h_rhs_x : ‖x‖ ^ 2 = ∑ j : n, ‖x.ofLp j‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
    have hsum : ∑ i : m, ‖(B *ᵥ x.ofLp) i‖ ^ 2 ≤
        (maxColSum B * maxRowSum B) * ∑ j : n, ‖x.ofLp j‖ ^ 2 := by
      calc
        ∑ i : m, ‖(B *ᵥ x.ofLp) i‖ ^ 2
            ≤ ∑ i : m, maxRowSum B * ∑ j : n, ‖B i j‖ * ‖x.ofLp j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => AuxClaim61.row_bound B x.ofLp i
        _ = maxRowSum B * ∑ i : m, ∑ j : n, ‖B i j‖ * ‖x.ofLp j‖ ^ 2 := by
          rw [Finset.mul_sum]
        _ = maxRowSum B * ∑ j : n, (∑ i : m, ‖B i j‖) * ‖x.ofLp j‖ ^ 2 := by
          rw [Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
        _ ≤ maxRowSum B * ∑ j : n, maxColSum B * ‖x.ofLp j‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (AuxClaim61.maxRowSum_nonneg B)
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (AuxClaim61.le_maxColSum B j) (sq_nonneg _)
        _ = (maxColSum B * maxRowSum B) * ∑ j : n, ‖x.ofLp j‖ ^ 2 := by
          rw [← Finset.mul_sum]
          ring
    have hsq : ‖(Matrix.toEuclideanLin B).toContinuousLinearMap x‖ ^ 2 ≤
        (Real.sqrt (maxColSum B * maxRowSum B) * ‖x‖) ^ 2 := by
      rw [h_lhs, mul_pow, Real.sq_sqrt hprod, h_rhs_x]
      exact hsum
    exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  calc
    specNorm B ^ 2 ≤ Real.sqrt (maxColSum B * maxRowSum B) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = maxColSum B * maxRowSum B := Real.sq_sqrt hprod
