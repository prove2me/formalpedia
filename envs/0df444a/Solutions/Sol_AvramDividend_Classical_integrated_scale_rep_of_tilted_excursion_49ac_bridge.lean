-- Prove2me | solution 1 for AvramDividend.Classical.integrated_scale_rep_of_tilted_excursion_49ac_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:06:15.642704+00:00
-- url     : https://prove2.me/submissions/c2b1f98c-141b-47d2-b467-a64f0f1f3582

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    (W V tail : ℝ → ℝ) (φ : ℝ)
    (hEsscher : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hExcursion : ∀ a b : ℝ, 0 < a → a ≤ b → V b = V a * Real.exp (∫ t in a..b, tail t))
    (hTail : ContinuousOn tail (Ioi (0 : ℝ))) :
    ∀ a b : ℝ, 0 < a → a ≤ b → W b = W a * Real.exp (∫ t in a..b, φ + tail t) := by
  intro a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsub : Set.uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have h1 : IntervalIntegrable tail volume a b := (hTail.mono hsub).intervalIntegrable
  have hsplit : (∫ t in a..b, φ + tail t) = φ * (b - a) + ∫ t in a..b, tail t := by
    rw [intervalIntegral.integral_add intervalIntegrable_const h1]
    simp
    ring
  rw [hsplit, hEsscher b hb, hEsscher a ha, hExcursion a b ha hab, Real.exp_add]
  have : Real.exp (φ * b) = Real.exp (φ * a) * Real.exp (φ * (b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  ring
