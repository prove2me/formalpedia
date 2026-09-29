-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.norm_weighted_kin_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:28.0823+00:00
-- url     : https://prove2.me/submissions/f15aeb73-88b8-4f72-ad66-76af7cd6e87f

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.norm_weighted_kin_le
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
import Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_weighted_kin_sq
open BookProof.GaussCoreQuadBounds









open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {kappa : Fin D → ℝ} {km : ℝ} (hkm : 0 ≤ km)
    (hk : ∀ j, |kappa j| ≤ km) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (∑ j : Fin D, ((kappa j : ℝ) : ℂ) • coreD j (coreD j p))‖
      ≤ km * ‖pgLp (kinPoly p)‖ := by

  have hkin : ‖pgLp (kinPoly p)‖ ^ 2
      = ∑ j : Fin D, ∑ k : Fin D, ‖pgLp (coreD k (coreD j p))‖ ^ 2 := by
    have h := norm_weighted_kin_sq (fun _ => (1 : ℝ)) p
    have hsum : (∑ j : Fin D, (((1 : ℝ) : ℂ)) • coreD j (coreD j p)) = -kinPoly p := by
      rw [kinPoly, neg_neg]
      exact Finset.sum_congr rfl fun j _ => by simp
    rw [hsum] at h
    have hneg : pgLp (-kinPoly p) = -pgLp (kinPoly p) := by
      rw [← pgMap_apply, ← pgMap_apply, map_neg]
    rw [hneg, norm_neg] at h
    simpa using h
  have hbound : ‖pgLp (∑ j : Fin D, ((kappa j : ℝ) : ℂ) • coreD j (coreD j p))‖ ^ 2
      ≤ (km * ‖pgLp (kinPoly p)‖) ^ 2 := by
    rw [norm_weighted_kin_sq, mul_pow, hkin, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hjk : kappa j * kappa k ≤ km ^ 2 := by
      have h1 := abs_le.mp (hk j)
      have h2 := abs_le.mp (hk k)
      nlinarith
    exact mul_le_mul_of_nonneg_right hjk (sq_nonneg _)
  have hrhs : 0 ≤ km * ‖pgLp (kinPoly p)‖ := mul_nonneg hkm (norm_nonneg _)
  nlinarith [norm_nonneg (pgLp (∑ j : Fin D, ((kappa j : ℝ) : ℂ) • coreD j (coreD j p)))]
