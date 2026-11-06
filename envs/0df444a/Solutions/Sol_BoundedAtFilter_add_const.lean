-- Prove2me | solution 1 for BoundedAtFilter.add_const
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:00:18.024002+00:00
-- url     : https://prove2.me/submissions/821afd54-46d0-40ed-a9ef-e0bdbe7b9142

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

open Filter

theorem solution {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  constructor
  · intro h
    have h' := h.add (const_boundedAtFilter atTop (-c))
    have heq : (fun n => u n + c) + Function.const ℕ (-c) = u := by
      funext n
      simp
    rw [heq] at h'
    simpa using! h'
  · intro h
    have h' := h.add (const_boundedAtFilter atTop c)
    simpa using! h'
