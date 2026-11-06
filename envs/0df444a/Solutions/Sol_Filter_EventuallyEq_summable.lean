-- Prove2me | solution 1 for Filter.EventuallyEq.summable
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:25:11.459802+00:00
-- url     : https://prove2.me/submissions/2537b163-b9a5-4308-ab99-ba88f9f0d64c

import Mathlib.Analysis.Normed.Group.Tannery

open Filter

theorem solution {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u := by
  exact hu.congr_atTop h.symm
