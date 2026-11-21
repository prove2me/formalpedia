-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tail_integral_shift_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T22:42:48.818179+00:00
-- url     : https://prove2.me/submissions/e479fbca-e6fb-4994-9115-5c9d02243582

import Mathlib
open MeasureTheory Set

theorem solution (κ : ℝ → ℝ) (Φ s : ℝ)
    (hNext : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-((Φ + s) * t))) * κ t) (Ioi (0 : ℝ)))
    (hBase : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-(Φ * t))) * κ t) (Ioi (0 : ℝ))) :
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-((Φ + s) * t))) * κ t) -
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-(Φ * t))) * κ t) =
    (∫ t in Ioi (0 : ℝ),
      Real.exp (-(Φ * t)) * (1 - Real.exp (-(s * t))) * κ t) := by
  have hpt (t : ℝ) :
      (1 - Real.exp (-((Φ + s) * t))) * κ t -
        (1 - Real.exp (-(Φ * t))) * κ t =
      Real.exp (-(Φ * t)) * (1 - Real.exp (-(s * t))) * κ t := by
    have he : Real.exp (-((Φ + s) * t)) =
        Real.exp (-(Φ * t)) * Real.exp (-(s * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  calc
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-((Φ + s) * t))) * κ t) -
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-(Φ * t))) * κ t) =
      (∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-((Φ + s) * t))) * κ t -
        (1 - Real.exp (-(Φ * t))) * κ t) := by
          exact (integral_sub hNext hBase).symm
    _ = (∫ t in Ioi (0 : ℝ),
      Real.exp (-(Φ * t)) * (1 - Real.exp (-(s * t))) * κ t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact hpt t
