-- Prove2me | solution 1 for Freiman.gap_centered_membership
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:39:45.542321+00:00
-- url     : https://prove2.me/submissions/c81b4da8-eb73-4f7e-a0e3-82fa64137dcf

import Definitions.Def_Freiman_gapModel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Freiman

theorem solution (a : ℤ → ℕ+) (t : ℝ) (hmax : ∀ i, localValue a i ≤ t)
    (h0 : localValue a 0 = t) : t ∈ symbolicMarkovSpectrum := by
  refine ⟨a, hmax, ?_⟩
  intro ε hε
  refine ⟨0, ?_⟩
  rw [h0]
  linarith
