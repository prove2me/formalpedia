-- Prove2me | solution 1 for BookProof.ChapterSirkSpectralGeometry.realSegment_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:10:05.798962+00:00
-- url     : https://prove2.me/submissions/2d097199-a309-4992-9298-de27fcd530c8

-- Generated from ChapterSirkSpectralGeometry.lean — solution of BookProof.ChapterSirkSpectralGeometry.realSegment_subset_closedBall
import Mathlib
import Definitions.Def_ChapterSirkSpectralGeometry
open BookProof.ChapterSirkSpectralGeometry









noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution {a b : ℝ} (ha : 0 ≤ a) :
    realSegment a b ⊆ Metric.closedBall (0 : ℂ) b := by

  rintro z ⟨hzi, hzl, hzu⟩
  have hz : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hzi]
  simp only [Metric.mem_closedBall, dist_zero_right]
  rw [hz]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans ha hzl)]
  exact hzu
