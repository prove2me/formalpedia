-- Prove2me | solution 1 for Freiman.gap_lower_binding
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:21:58.853005+00:00
-- url     : https://prove2.me/submissions/da8e64e1-3e3e-48df-8b30-613c2169d21a

import Mathlib.Tactic.IntervalCases
import Definitions.Def_Freiman_gapCertificateData

open Freiman

theorem solution : gapLowerRows.length = 19 ∧ gapLowerTrees.length = 19 ∧ ∀ n : ℕ, n < 19 → gapRoot (gapLowerTrees[n]!) = (gapLowerRows[n]!).state := by
  refine ⟨rfl, rfl, ?_⟩
  intro n hn
  interval_cases n <;> rfl

