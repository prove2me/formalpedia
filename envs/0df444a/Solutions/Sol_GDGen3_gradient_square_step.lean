-- Prove2me | solution 1 for GDGen3.gradient_square_step
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:46:03.667569+00:00
-- url     : https://prove2.me/submissions/4b461007-16b3-4547-9ea8-b452dcfe15eb

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_gradient_square_step

lemma ginner_forward (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P i (i + 1) = h * P (i + 1) i := by
  unfold ginner
  rw [sum_range_succ]
  ring

lemma ginner_backward (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P (i + 1) i = -h * P i i := by
  unfold ginner
  rw [sum_range_succ]
  ring

lemma adjacent_interpolation_sum (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ i j, P i j = P j i) (i : ℕ) :
    2 * (Qv h f P i (i + 1) + Qv h f P (i + 1) i) =
      h * (P i i - P (i + 1) (i + 1))
        - (2 - h) * (P i i + P (i + 1) (i + 1) - 2 * P i (i + 1)) := by
  unfold Qv
  rw [ginner_forward, ginner_backward, hP (i + 1) i]
  ring

end GDGen3Proof_gradient_square_step

open GDGen3Proof_gradient_square_step

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
