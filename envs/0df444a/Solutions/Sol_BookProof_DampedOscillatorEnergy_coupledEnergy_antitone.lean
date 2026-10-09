-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.coupledEnergy_antitone
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:46:30.11241+00:00
-- url     : https://prove2.me/submissions/a9adc777-d1d9-4306-bd59-473ad41c91d4

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.coupledEnergy_antitone
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
import Theorems.Thm_BookProof_DampedOscillatorEnergy_hasDerivAt_coupledEnergy
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution {lam1 lam2 omega1 omega2 c : ℝ} {x1 x2 v1 v2 a1 a2 : ℝ → ℝ}
    (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2)
    (hx1 : ∀ t, HasDerivAt x1 (v1 t) t) (hx2 : ∀ t, HasDerivAt x2 (v2 t) t)
    (hv1 : ∀ t, HasDerivAt v1 (a1 t) t) (hv2 : ∀ t, HasDerivAt v2 (a2 t) t)
    (heq1 : ∀ t, a1 t + lam1 * v1 t + omega1 ^ 2 * x1 t - c * x2 t = 0)
    (heq2 : ∀ t, a2 t + lam2 * v2 t + omega2 ^ 2 * x2 t - c * x1 t = 0) :
    Antitone (coupledEnergy omega1 omega2 c x1 x2 v1 v2) := by

  refine antitone_of_deriv_nonpos
    (fun t => (hasDerivAt_coupledEnergy hx1 hx2 hv1 hv2 heq1 heq2 t).differentiableAt)
    (fun t => ?_)
  rw [(hasDerivAt_coupledEnergy hx1 hx2 hv1 hv2 heq1 heq2 t).deriv]
  have p1 : 0 ≤ lam1 * v1 t ^ 2 := mul_nonneg hlam1 (sq_nonneg _)
  have p2 : 0 ≤ lam2 * v2 t ^ 2 := mul_nonneg hlam2 (sq_nonneg _)
  linarith
