-- Prove2me | solution 2 for GDGen3.rV_sub_U
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:29:17.537254+00:00
-- url     : https://prove2.me/submissions/d4ab9459-0482-4ca3-b962-1b631ecab1a7

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_Abar_ne_zero
import Theorems.Thm_GDGen3_ell_of_lt
import Theorems.Thm_GDGen3_ell_of_gt
import Theorems.Thm_GDGen3_am_telescope
import Theorems.Thm_GDGen3_D_telescope

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N i : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (h0 : ξ 0 = 0)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (hr : r ≠ 0) (hi : i + 1 ≤ N) :
    r * V r ξ N i - U r ξ N i = (1 - r ^ 2) / 2 := by
  have hV : V r ξ N i = (Am ξ i + r * Abar ξ i) * D r ξ N (i + 1) := by
    unfold V
    have ht : ∀ j ∈ Icc (i + 1) N, ell r ξ N j i =
        (Am ξ i + r * Abar ξ i) * (D r ξ N j - D r ξ N (j + 1)) := by
      intro j hj
      exact ell_of_gt r ξ N (by simp only [mem_Icc] at hj; omega)
    rw [sum_congr rfl ht, ← mul_sum, D_telescope r ξ N i hi]
  have hU : U r ξ N i = (D r ξ N i + r * D r ξ N (i + 1)) * Am ξ i := by
    unfold U
    have ht : ∀ j ∈ range i, ell r ξ N j i =
        (Abar ξ j - Am ξ j) * (D r ξ N i + r * D r ξ N (i + 1)) := by
      intro j hj
      exact ell_of_lt r ξ N (mem_range.mp hj)
    rw [sum_congr rfl ht, ← sum_mul]
    cases i with
    | zero => simp [Am]
    | succ k => rw [am_telescope ξ k]; simp [Am, mul_comm]
  have hAD : Abar ξ i * D r ξ N (i + 1) = pj r (i + 1) := by
    simp only [D, if_neg (by omega : ¬(i + 1 = 0 ∨ N < i + 1)),
      Am, if_neg (by omega : i + 1 ≠ 0), Nat.add_sub_cancel]
    exact mul_div_cancel₀ _ (Abar_ne_zero ξ h0 hpos i)
  have hamD : Am ξ i * D r ξ N i = pj r i := by
    by_cases hi0 : i = 0
    · subst i; simp [Am, D, pj]
    · simp only [D, if_neg (by omega : ¬(i = 0 ∨ N < i))]
      have ha : Am ξ i ≠ 0 := by
        simpa [Am, hi0] using Abar_ne_zero ξ h0 hpos (i - 1)
      exact mul_div_cancel₀ _ ha
  have hp : r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by
    simp only [pj, Nat.mul_add, pow_add]
    field_simp
    ring
  calc
    r * V r ξ N i - U r ξ N i =
        r ^ 2 * (Abar ξ i * D r ξ N (i + 1)) - Am ξ i * D r ξ N i := by
      rw [hV, hU]; ring
    _ = r ^ 2 * pj r (i + 1) - pj r i := by rw [hAD, hamD]
    _ = (1 - r ^ 2) / 2 := hp
