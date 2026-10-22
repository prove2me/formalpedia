-- Prove2me | solution 1 for GDGen3.interpolation_scaling
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:44:06.119978+00:00
-- url     : https://prove2.me/submissions/94f9393a-1121-4ef0-8d69-0788092f84d6

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (a s h : ℝ) (he : h = s * a) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (i j : ℕ) :
    Qv a (fun k => s * f k) (fun k l => s ^ 2 * P k l) i j =
      s * Qv h f P i j + s * (1 - s) / 2 * (P i i + P j j - 2 * P i j) := by
  unfold Qv ginner
  simp only [← mul_sum]
  rw [he]
  ring
