-- Prove2me | solution 2 for GDGen3.D_root_step
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:55:35.827471+00:00
-- url     : https://prove2.me/submissions/fddbdbf9-ee67-4783-810e-c280f5a3af38

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_rootXi_pos
import Theorems.Thm_GDGen3_Abar_root_pos
import Theorems.Thm_GDGen3_Abar_root_recur
import Theorems.Thm_GDGen3_rootXi_step_scaled

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    D r (rootXi r N) N (i + 1) < D r (rootXi r N) N i := by
  have hA := Abar_root_pos r hr hr1 N i
  have hAp := Abar_root_pos r hr hr1 N (i - 1)
  have hx := rootXi_pos r hr hr1 N i (by omega)
  have hsc := rootXi_step_scaled r hr hr1 N i hi hiN hbranch
  have hscA := mul_lt_mul_of_pos_right hsc hAp
  have hrec : Abar (rootXi r N) i * rootXi r N i =
      Abar (rootXi r N) (i - 1) * (1 + rootXi r N (i - 1)) := by
    rw [Abar_root_recur r N i hi, div_mul_cancel₀ _ (ne_of_gt hx)]
  have hmain : pj r (i + 1) * Abar (rootXi r N) (i - 1) < pj r i * Abar (rootXi r N) i := by
    apply (mul_lt_mul_iff_right₀ hx).mp
    calc
      _ = pj r (i + 1) * rootXi r N i * Abar (rootXi r N) (i - 1) := by ring
      _ < pj r i * (1 + rootXi r N (i - 1)) * Abar (rootXi r N) (i - 1) := hscA
      _ = _ := by linear_combination -pj r i * hrec
  simp only [D, if_neg (by omega : ¬(i + 1 = 0 ∨ N < i + 1)),
    if_neg (by omega : ¬(i = 0 ∨ N < i)), Am, if_neg (by omega : i + 1 ≠ 0),
    if_neg (by omega : i ≠ 0), Nat.add_sub_cancel]
  exact (div_lt_div_iff₀ hA hAp).2 hmain
