-- Prove2me | solution 1 for FamousTheorems.ratio_test_dalembert_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:30:38.404753+00:00
-- url     : https://prove2.me/submissions/29c84132-0182-4c4a-95db-512b4b34ea2f

import Mathlib

theorem solution {α : Type*} [SeminormedAddCommGroup α] [CompleteSpace α] {f : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ᶠ n in Filter.atTop, ‖f (n + 1)‖ ≤ r * ‖f n‖) : Summable f :=
  summable_of_ratio_norm_eventually_le hr h
