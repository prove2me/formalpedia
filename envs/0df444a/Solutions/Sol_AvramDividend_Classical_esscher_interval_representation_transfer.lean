-- Prove2me | solution 1 for AvramDividend.Classical.esscher_interval_representation_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:56:38.386384+00:00
-- url     : https://prove2.me/submissions/40cfb14d-d696-4fd1-8f45-7b835187a16d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem solution
    (W V : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0))
    (htilt : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hint : ∀ a b : ℝ, 0 < a → a ≤ b →
      V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t))) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t)) := by
  intro a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le ha ht.1
  have htailint :
      IntervalIntegrable (fun t : ℝ => μ.real (Ici t)) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hcont.mono hsub)
  have hsplit :
      (∫ t in a..b, φ + μ.real (Ici t)) =
        (b - a) * φ + (∫ t in a..b, μ.real (Ici t)) := by
    calc
      _ = (∫ _ in a..b, φ) + (∫ t in a..b, μ.real (Ici t)) := by
        simpa only using
          (intervalIntegral.integral_add
            (intervalIntegrable_const) htailint)
      _ = (b - a) * φ + (∫ t in a..b, μ.real (Ici t)) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
  have hexp_phi :
      Real.exp (φ * b) =
        Real.exp (φ * a) * Real.exp ((b - a) * φ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    W b = Real.exp (φ * b) * V b := htilt b hb
    _ = Real.exp (φ * b) *
          (V a * Real.exp (∫ t in a..b, μ.real (Ici t))) := by
        rw [hint a b ha hab]
    _ = (Real.exp (φ * a) * V a) *
          Real.exp (∫ t in a..b, φ + μ.real (Ici t)) := by
        rw [hsplit, Real.exp_add, hexp_phi]
        ring
    _ = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t)) := by
        rw [htilt a ha]
