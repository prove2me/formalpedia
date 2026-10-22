-- Prove2me | solution 1 for GDGen3.pj_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:15:33.481581+00:00
-- url     : https://prove2.me/submissions/505a9be4-f5f9-49d6-a8f7-df0e3ebe3bf8

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : r ≠ 0) (N : ℕ) :
    2 * pj r N = r ^ (-(2 * (N : ℤ))) - 1 := by
  rw [zpow_neg]
  have he : (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) := by simp
  rw [he, zpow_natCast]
  unfold pj
  field_simp
