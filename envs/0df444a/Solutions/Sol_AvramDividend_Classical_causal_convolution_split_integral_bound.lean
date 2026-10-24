-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_split_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:16:48.567485+00:00
-- url     : https://prove2.me/submissions/ca742a50-1190-4685-9021-c239d7a299ec

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Splitting a causal convolution bounds its two pieces by kernel and input masses. -/
theorem solution
    (κ F : ℝ → ℝ) (x u A B M ρ : ℝ)
    (h0u : 0 ≤ u) (hux : u ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleftInt : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume 0 u)
    (hrightInt : IntervalIntegrable
      (fun s : ℝ => κ (x - s) * F s) volume u x)
    (hFInt : IntervalIntegrable F volume 0 u)
    (hκInt : IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x)
    (hKleft : ∀ s ∈ Ioo (0 : ℝ) u, κ (x - s) ≤ A)
    (hFzero : ∀ s ∈ Ioo (0 : ℝ) u, 0 ≤ F s)
    (hFright : ∀ s ∈ Ioo u x, F s ≤ B)
    (hκzero : ∀ s ∈ Ioo u x, 0 ≤ κ (x - s))
    (hFmass : (∫ s in (0 : ℝ)..u, F s) ≤ M)
    (hκmass : (∫ s in u..x, κ (x - s)) ≤ ρ) :
    (∫ s in (0 : ℝ)..x, κ (x - s) * F s) ≤ A * M + B * ρ := by
  have hleftPoint : ∀ s ∈ Ioo (0 : ℝ) u,
      κ (x - s) * F s ≤ A * F s := by
    intro s hs
    exact mul_le_mul_of_nonneg_right (hKleft s hs) (hFzero s hs)
  have hleft :
      (∫ s in (0 : ℝ)..u, κ (x - s) * F s) ≤ A * M := by
    calc
      (∫ s in (0 : ℝ)..u, κ (x - s) * F s)
          ≤ ∫ s in (0 : ℝ)..u, A * F s :=
            intervalIntegral.integral_mono_on_of_le_Ioo
              h0u hleftInt (hFInt.const_mul A) hleftPoint
      _ = A * (∫ s in (0 : ℝ)..u, F s) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ A * M := mul_le_mul_of_nonneg_left hFmass hA
  have hrightPoint : ∀ s ∈ Ioo u x,
      κ (x - s) * F s ≤ B * κ (x - s) := by
    intro s hs
    calc
      κ (x - s) * F s ≤ κ (x - s) * B :=
        mul_le_mul_of_nonneg_left (hFright s hs) (hκzero s hs)
      _ = B * κ (x - s) := mul_comm _ _
  have hright :
      (∫ s in u..x, κ (x - s) * F s) ≤ B * ρ := by
    calc
      (∫ s in u..x, κ (x - s) * F s)
          ≤ ∫ s in u..x, B * κ (x - s) :=
            intervalIntegral.integral_mono_on_of_le_Ioo
              hux hrightInt (hκInt.const_mul B) hrightPoint
      _ = B * (∫ s in u..x, κ (x - s)) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ B * ρ := mul_le_mul_of_nonneg_left hκmass hB
  calc
    (∫ s in (0 : ℝ)..x, κ (x - s) * F s)
        = (∫ s in (0 : ℝ)..u, κ (x - s) * F s) +
          (∫ s in u..x, κ (x - s) * F s) :=
            (intervalIntegral.integral_add_adjacent_intervals
              hleftInt hrightInt).symm
    _ ≤ A * M + B * ρ := add_le_add hleft hright
