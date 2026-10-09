-- Prove2me | solution 1 for BookProof.ChapterAngularMomentum.circHarm_rotate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:37:42.350855+00:00
-- url     : https://prove2.me/submissions/b7733626-1785-4d8a-906f-01ec2f9c44c4

-- Generated from ChapterAngularMomentum.lean — solution of BookProof.ChapterAngularMomentum.circHarm_rotate
import Mathlib
import Definitions.Def_ChapterAngularMomentum
open BookProof.ChapterAngularMomentum




open Complex

set_option maxHeartbeats 1000000 in
theorem solution (μ : ℕ) (t : ℝ) (z : ℂ) :
    circHarm μ (Complex.exp ((t : ℂ) * Complex.I) * z)
      = Complex.exp ((μ : ℂ) * (t : ℂ) * Complex.I) * circHarm μ z := by

  have hnorm : ‖Complex.exp ((t : ℂ) * Complex.I) * z‖ = ‖z‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  rw [circHarm, circHarm, hnorm, mul_div_assoc, mul_pow, ← Complex.exp_nat_mul]
  ring_nf
