-- Prove2me | solution 1 for GDGen3.adjacent_interpolation_sum
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:45:46.705171+00:00
-- url     : https://prove2.me/submissions/d6f0e436-c479-4320-9d92-cad13b667a46

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_adjacent_interpolation_sum

lemma ginner_forward (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P i (i + 1) = h * P (i + 1) i := by
  unfold ginner
  rw [sum_range_succ]
  ring

lemma ginner_backward (h : ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ginner h P (i + 1) i = -h * P i i := by
  unfold ginner
  rw [sum_range_succ]
  ring

end GDGen3Proof_adjacent_interpolation_sum

open GDGen3Proof_adjacent_interpolation_sum

theorem solution (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ i j, P i j = P j i) (i : ℕ) :
    2 * (Qv h f P i (i + 1) + Qv h f P (i + 1) i) =
      h * (P i i - P (i + 1) (i + 1))
        - (2 - h) * (P i i + P (i + 1) (i + 1) - 2 * P i (i + 1)) := by
  unfold Qv
  rw [ginner_forward, ginner_backward, hP (i + 1) i]
  ring
