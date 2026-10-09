-- Prove2me | solution 1 for BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:38:17.628086+00:00
-- url     : https://prove2.me/submissions/fc6cf707-8133-4ab6-b4b7-c046f9bf6529

-- Generated from ChapterAngularMomentum.lean — solution of BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen
import Mathlib
import Definitions.Def_ChapterAngularMomentum
import Theorems.Thm_BookProof_ChapterAngularMomentum_angularMomentum_eigen
import Theorems.Thm_BookProof_ChapterAngularMomentum_circHarm_rotate
import Theorems.Thm_BookProof_ChapterAngularMomentum_circHarm_differentiableAt
open BookProof.ChapterAngularMomentum




open Complex

set_option maxHeartbeats 1000000 in
theorem solution (μ : ℕ) {z : ℂ} (hz : z ≠ 0) :
    -Complex.I * (z.re * fderiv ℝ (circHarm μ) z Complex.I
        - z.im * fderiv ℝ (circHarm μ) z 1)
      = (μ : ℂ) * circHarm μ z :=
  angularMomentum_eigen (μ := (μ : ℝ)) (circHarm_differentiableAt hz)
      (by intro t; simpa using circHarm_rotate μ t z)
