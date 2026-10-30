-- Prove2me | solution 1 for AvramDividend.Classical.antitone_tail_interval_lower_bound_49ac_gap
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:49:10.940689+00:00
-- url     : https://prove2.me/submissions/b1d08739-e6bc-4a50-b918-f86f9b04b75f

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    (T : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hTcont : ContinuousOn T (uIcc (x / 2) x))
    (hTanti : AntitoneOn T (Ioi (0 : ℝ))) :
    T x * (x - x / 2) ≤ ∫ t in (x / 2)..x, T t := by
  have hle : x / 2 ≤ x := by linarith
  have hint : IntervalIntegrable T volume (x / 2) x := hTcont.intervalIntegrable
  have hc : IntervalIntegrable (fun _ : ℝ => T x) volume (x / 2) x := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on hle hc hint (by
    intro t ht
    exact hTanti (show (0:ℝ) < t by linarith [ht.1]) (show (0:ℝ) < x from hx) ht.2)
  simp at h
  linarith
