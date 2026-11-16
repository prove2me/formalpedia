-- Prove2me | solution 1 for FixedKMachine.normalization
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:55:52.219893+00:00
-- url     : https://prove2.me/submissions/338af8c6-b372-4d11-8f16-5070a105aa64

import Mathlib
open MeasureTheory Set

theorem solution (n k a f ef g : ℝ) (hn : 0 < n) (hk : 0 ≤ k)
    (hr : g = (n*f-ef)/(n+k)) :
    (a*(n+k)/n)*g = a*f-a*ef/n := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hnk0 : n+k ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hn hk)
  rw [hr]
  field_simp [hn0, hnk0]
  <;> ring
