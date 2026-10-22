-- Prove2me | solution 1 for GDGen3.V_last
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:14:36.29769+00:00
-- url     : https://prove2.me/submissions/23a81a42-191e-4cb4-8c2b-ead34feab9fd

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) : V r ξ N N = 0 := by
  simp [V]
