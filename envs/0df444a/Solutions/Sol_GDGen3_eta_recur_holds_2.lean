-- Prove2me | solution 2 for GDGen3.eta_recur_holds
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:29:14.598526+00:00
-- url     : https://prove2.me/submissions/fd3d3f84-2b00-4a49-bc39-f4705cc1c17b

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_Abar_ne_zero

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1)) :
    eta_recur_prop r N ξ := by
  intro i hi hiN
  have h6 : pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i := hquad i (by omega)
  have h7 : pj r i * eta r N ξ (i - 1) * (1 + ξ (i - 1)) = X r N i := by
    have h := hquad7 (i - 1) (by omega)
    have hidx : i - 1 + 1 = i := by omega
    simpa only [hidx] using h
  have hA : Abar ξ i = Abar ξ (i - 1) * (1 + ξ (i - 1)) / ξ i := by
    have hi1 : i = (i - 1) + 1 := by omega
    conv_lhs => rw [hi1]
    rw [Abar]
    have : i - 1 + 1 = i := by omega
    rw [this]
  have hAne : Abar ξ (i - 1) ≠ 0 := Abar_ne_zero ξ h0 hpos (i - 1)
  have hxne : ξ i ≠ 0 := ne_of_gt (hpos i (by omega))
  have h1ne : 1 + ξ (i - 1) ≠ 0 := by
    by_cases hi0 : i - 1 = 0
    · simp [hi0, h0]
    · have := hpos (i - 1) hi0; linarith
  have hD : D r ξ N i = pj r i / Abar ξ (i - 1) := by
    rw [D, if_neg (by omega : ¬ (i = 0 ∨ N < i)), Am,
        if_neg (by omega : ¬ i = 0)]
  have hD1 : D r ξ N (i + 1) = pj r (i + 1) / Abar ξ i := by
    have h0 : ¬ (i + 1 = 0 ∨ N < i + 1) := by omega
    have h2 : i + 1 - 1 = i := by omega
    rw [D, if_neg h0, Am, if_neg (by omega : ¬ i + 1 = 0), h2]
  have key : eta r N ξ (i - 1) * (pj r i) * (1 + ξ (i - 1))
      = pj r (i + 1) * (1 + eta r N ξ i) * ξ i := by
    linear_combination h7 - h6
  rw [hD, hD1, hA]
  field_simp
  linear_combination key
