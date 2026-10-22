-- Prove2me | solution 1 for GDGen3.small_history_split
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:47:10.6678+00:00
-- url     : https://prove2.me/submissions/1e26e538-1127-4bd8-ad93-2f7b47030b29

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (N : ℕ) (a s h : ℝ) (he : h = s * a) (f q : ℕ → ℝ) :
    smallK N h f q = scaledK N a s f q
      + (1 - s) * ((∑ i ∈ range N, q i) - (N : ℝ) * q N) := by
  unfold smallK scaledK
  rw [he]
  ring
