-- Prove2me | solution 2 for GDGen3.flow_at_index
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:38:34.758916+00:00
-- url     : https://prove2.me/submissions/e004f006-0f68-42a3-9986-5012edef3d4c

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_flow_identity

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) (i : ℕ) (hi : i < N) :
    d r ξ N i = M r N := by
  have h := flow_identity r N hN ξ hr hr1 hpos h0 hquad hquad7 hpin i (by omega)
  by_cases hi0 : i = 0
  · subst i; simpa using h
  · have hprev := flow_identity r N hN ξ hr hr1 hpos h0 hquad hquad7 hpin (i - 1) (by omega)
    have hid : i - 1 + 1 = i := by omega
    rw [hid] at hprev
    have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast hid
    rw [hcast] at hprev
    rw [sum_range_succ] at h
    norm_num only [Nat.cast_add, Nat.cast_one] at h
    linarith
