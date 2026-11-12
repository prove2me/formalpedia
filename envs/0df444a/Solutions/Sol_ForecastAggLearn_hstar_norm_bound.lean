-- Prove2me | solution 1 for ForecastAggLearn.hstar_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:13:09.008215+00:00
-- url     : https://prove2.me/submissions/d1aa2a9e-2afd-4a8a-8c75-e9090ab40984

import Definitions.Def_ForecastAggLearn_hstar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open ForecastAggLearn
open scoped BigOperators

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hA : ∀ y : EuclideanSpace ℝ (Fin m),
      σ * ‖y‖ ≤ ‖(WithLp.toLp 2 (A.mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 (hstar A) : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ m / σ ^ 2 ∧ m ≤ n ∧
      ‖(WithLp.toLp 2 (hstar A) : EuclideanSpace ℝ (Fin n))‖ ≤ Real.sqrt n / σ := by
  have hInj : Function.Injective A.mulVec := by
    intro x y hxy
    have h := hA (WithLp.toLp 2 (x - y))
    have hz : A.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    rw [WithLp.ofLp_toLp, hz, WithLp.toLp_zero, norm_zero] at h
    have hnorm : ‖(WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin m))‖ = 0 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin m))]
    have hz' := congrArg WithLp.ofLp (norm_eq_zero.mp hnorm)
    simpa only [WithLp.ofLp_toLp, WithLp.ofLp_zero, sub_eq_zero] using hz'
  have hG : Function.Injective (A.transpose * A).mulVec := by
    intro x y hxy
    have hz : (A.transpose * A).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have hs := Matrix.dotProduct_transpose_mulVec A (x - y) (A.mulVec (x - y))
    rw [Matrix.mulVec_mulVec, hz, dotProduct_zero] at hs
    have hAz : A.mulVec (x - y) = 0 := dotProduct_self_eq_zero.mp hs.symm
    apply sub_eq_zero.mp
    apply hInj
    simpa only [Matrix.mulVec_zero] using hAz
  have hdet : IsUnit (A.transpose * A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hG)
  have hdim : m ≤ n := by
    simpa using (LinearMap.finrank_le_finrank_of_injective (f := A.toLin') hInj)
  let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 ((A.transpose * A)⁻¹.mulVec (fun _ => 1))
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (hstar A)
  let o : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun _ => 1)
  have hvo : ‖w‖ ^ 2 = inner ℝ v o := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [w, v, o, EuclideanSpace.inner_toLp_toLp, star_trivial]
    unfold hstar
    rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact dotProduct_comm _ _
  have ho : ‖o‖ ^ 2 = m := by simp [o, EuclideanSpace.real_norm_sq_eq]
  have hAv : σ * ‖v‖ ≤ ‖w‖ := by simpa [v, w, hstar] using hA v
  have hcs : ‖w‖ ^ 2 ≤ ‖v‖ * ‖o‖ := hvo ▸ real_inner_le_norm v o
  have hsw : σ * ‖w‖ ≤ ‖o‖ := by
    by_cases hw : ‖w‖ = 0
    · rw [hw, mul_zero]; exact norm_nonneg _
    · have hwpos : 0 < ‖w‖ := (norm_nonneg _).lt_of_ne' hw
      have hh : (σ * ‖w‖) * ‖w‖ ≤ ‖o‖ * ‖w‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hcs hσ.le,
          mul_le_mul_of_nonneg_right hAv (norm_nonneg o)]
      exact (mul_le_mul_iff_left₀ hwpos).mp hh
  have hsq : ‖w‖ ^ 2 ≤ m / σ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
    nlinarith [sq_le_sq₀ (mul_nonneg hσ.le (norm_nonneg w)) (norm_nonneg o) |>.mpr hsw]
  refine ⟨hsq, hdim, ?_⟩
  apply (le_div_iff₀ hσ).mpr
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hdim
  have hroot : ‖o‖ ≤ Real.sqrt n := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ), norm_nonneg o]
  simpa [w, mul_comm] using hsw.trans hroot

#print axioms solution

