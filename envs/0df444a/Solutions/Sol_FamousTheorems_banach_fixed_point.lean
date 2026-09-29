-- Prove2me | solution 1 for FamousTheorems.banach_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T01:51:32.918696+00:00
-- url     : https://prove2.me/submissions/abba46d9-e85d-408b-a4e5-e9f21ea4a80c

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem solution {α : Type*} [EMetricSpace α] [CompleteSpace α] {K : ℝ≥0} {f : α → α}
    (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ⊤) :
    ∃ y, Function.IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  ContractingWith.exists_fixedPoint hf x hx
