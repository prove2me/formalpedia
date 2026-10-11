-- Prove2me | solution 1 for BookProof.RadialMollifier.circle_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:21.37152+00:00
-- url     : https://prove2.me/submissions/b4a7a00d-df40-43a3-8525-4d703e8b6393

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.circle_integral_eq
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hh : DifferentiableOn ℂ h s)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall z r ⊆ s) :
    ∫ θ in (-π)..π, h (z - (r : ℂ) * Complex.exp (θ * Complex.I)) = ((2 * π : ℝ) : ℂ) * h z := by

  have e1 : ∀ θ : ℝ, z - (r : ℂ) * Complex.exp (θ * Complex.I) = circleMap z (-r) θ := by
    intro θ
    simp [circleMap]
    ring
  have hper : Function.Periodic (fun θ : ℝ => h (circleMap z (-r) θ)) (2 * π) := by
    intro θ
    simp [periodic_circleMap z (-r) θ]
  have hshift : (∫ θ in (-π)..π, h (circleMap z (-r) θ))
      = ∫ θ in (0 : ℝ)..(2 * π), h (circleMap z (-r) θ) := by
    have := hper.intervalIntegral_add_eq (-π) 0
    simpa [add_comm, two_mul] using this
  have habs : |(-r)| = r := by rw [abs_neg, abs_of_pos hr]
  have hcavg : circleAverage h z (-r) = h z := by
    refine circleAverage_of_differentiable_on_off_countable (s := (∅ : Set ℂ)) countable_empty ?_ ?_
    · rw [habs]
      exact (hh.continuousOn).mono hsub
    · intro w hw
      rw [habs] at hw
      exact hh.differentiableAt (hs.mem_nhds (hsub (ball_subset_closedBall hw.1)))
  simp only [e1]
  rw [hshift]
  have : (∫ θ in (0:ℝ)..(2 * π), h (circleMap z (-r) θ)) = (2 * π) • circleAverage h z (-r) := by
    rw [circleAverage_def, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_smul]
  rw [this, hcavg]
  simp [Complex.real_smul]
