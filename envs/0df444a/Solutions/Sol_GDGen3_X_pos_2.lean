-- Prove2me | solution 2 for GDGen3.X_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:37:45.29899+00:00
-- url     : https://prove2.me/submissions/d5be127b-f624-42de-80e8-cb1fb5983849

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_PiS_average_strictMono

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hi : 1 ≤ i) (hiN : i < N) :
    0 < X r N i := by
  have hNi : 1 ≤ N := by omega
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  have hcN : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hNi
  have hm := PiS_average_strictMono r hr hr1 (by omega : i - 1 < N - 1)
  dsimp at hm
  rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hNi] at hm
  have hci2 : ((i - 1 : ℕ) : ℝ) + 2 = (i : ℝ) + 1 := by linarith
  have hcN2 : ((N - 1 : ℕ) : ℝ) + 2 = (N : ℝ) + 1 := by linarith
  rw [hci, hcN, hci2, hcN2] at hm
  have hipos : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hc := (div_lt_div_iff₀ (by positivity) (by positivity)).mp hm
  unfold X M
  apply div_pos
  · have hden : 0 < (N : ℝ) * ((N : ℝ) + 1) := by positivity
    have hnum : 0 < (1 - r) *
        ((i : ℝ) * ((i : ℝ) + 1) * PiS r N - (N : ℝ) * ((N : ℝ) + 1) * PiS r i) :=
      mul_pos (by linarith) (by nlinarith [hc])
    have he : 2 * (1 - r) * PiS r N / ((N : ℝ) * ((N : ℝ) + 1)) * (i : ℝ) * ((i : ℝ) + 1) / 2
        - (1 - r) * PiS r i =
        ((1 - r) * ((i : ℝ) * ((i : ℝ) + 1) * PiS r N - (N : ℝ) * ((N : ℝ) + 1) * PiS r i)) /
          ((N : ℝ) * ((N : ℝ) + 1)) := by field_simp
    rw [he]
    exact div_pos hnum hden
  · positivity
