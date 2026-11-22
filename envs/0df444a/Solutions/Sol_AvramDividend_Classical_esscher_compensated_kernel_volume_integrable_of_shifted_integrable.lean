-- Prove2me | solution 1 for AvramDividend.Classical.esscher_compensated_kernel_volume_integrable_of_shifted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:27:56.980704+00:00
-- url     : https://prove2.me/submissions/66a2a29c-7199-4a81-b3b5-796daabcdf83

import Mathlib
open MeasureTheory Set

theorem solution (κ : ℝ → ℝ) (φ s : ℝ)
    (hNext : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-((φ + s) * t))) * κ t) (Ioi 0) (volume : Measure ℝ))
    (hBase : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-(φ * t))) * κ t) (Ioi 0) (volume : Measure ℝ)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(φ * t)) *
        (1 - Real.exp (-(s * t))) * κ t) (Ioi 0) (volume : Measure ℝ) := by
  have hp (t : ℝ) :
      Real.exp (-(φ * t)) * (1 - Real.exp (-(s * t))) * κ t =
        (1 - Real.exp (-((φ + s) * t))) * κ t -
        (1 - Real.exp (-(φ * t))) * κ t := by
    have he : Real.exp (-((φ + s) * t)) =
        Real.exp (-(φ * t)) * Real.exp (-(s * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have hFun : (fun t : ℝ => Real.exp (-(φ * t)) *
      (1 - Real.exp (-(s * t))) * κ t) =
      (fun t : ℝ => (1 - Real.exp (-((φ + s) * t))) * κ t) -
      (fun t : ℝ => (1 - Real.exp (-(φ * t))) * κ t) := by
    funext t
    exact hp t
  rw [hFun]
  exact hNext.sub hBase