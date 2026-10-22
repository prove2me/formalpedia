-- Prove2me | solution 2 for GDGen3.gradient_square_step
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:47:37.586865+00:00
-- url     : https://prove2.me/submissions/30f2a369-91ba-4c29-85a8-83241130dc2d

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_adjacent_interpolation_sum

noncomputable section

open Finset

open GDGen3

theorem solution (h : ℝ) (hh : 0 < h) (hh2 : h ≤ 2)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) (i : ℕ)
    (hQf : 0 ≤ Qv h f P i (i + 1)) (hQb : 0 ≤ Qv h f P (i + 1) i)
    (hdiff : 0 ≤ P i i + P (i + 1) (i + 1) - 2 * P i (i + 1)) :
    P (i + 1) (i + 1) ≤ P i i := by
  have he := adjacent_interpolation_sum h f P hP i
  have hnon := mul_nonneg (show 0 ≤ 2 - h by linarith) hdiff
  have hm : 0 ≤ h * (P i i - P (i + 1) (i + 1)) := by linarith
  by_contra hneg
  have hn := mul_neg_of_pos_of_neg hh (show P i i - P (i + 1) (i + 1) < 0 by linarith)
  linarith
