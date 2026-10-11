-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.integrable_bdd_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:51.787989+00:00
-- url     : https://prove2.me/submissions/78b11deb-f6ba-4447-8568-45bb3522afa8

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.integrable_bdd_mul
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (G : ℝ → ℂ) (hG : Integrable G) (u : ℝ → ℝ) (hu : Continuous u)
    (hb : ∀ x, |u x| ≤ 1) : Integrable (fun x : ℝ => (u x : ℂ) * G x) := by

  refine Integrable.bdd_mul (c := 1) hG
    ((Complex.continuous_ofReal.comp hu).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Complex.norm_real]
  exact hb x
