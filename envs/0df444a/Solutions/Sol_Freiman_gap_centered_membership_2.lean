-- Prove2me | solution 2 for Freiman.gap_centered_membership
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-10T12:48:12.852256+00:00
-- url     : https://prove2.me/submissions/d5030979-f181-4b92-a697-c0e3383f7044

import Definitions.Def_Freiman_gapModel

open Freiman

theorem solution (a : ℤ → ℕ+) (t : ℝ) (hmax : ∀ i, localValue a i ≤ t)
    (h0 : localValue a 0 = t) : t ∈ symbolicMarkovSpectrum := by
  refine ⟨a, hmax, ?_⟩
  intro ε hε
  exact ⟨0, by rw [h0]; linarith⟩
