-- Prove2me | solution 1 for Freiman.upper_large_model
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:37:54.581088+00:00
-- url     : https://prove2.me/submissions/e6854c44-db10-4852-af7b-4ad6cd220582

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_KA_bounds
import Theorems.Thm_Freiman_upper_large_data
import Theorems.Thm_Freiman_upper_large_noncentral
import Theorems.Thm_Freiman_upper_large_margin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (n : ℕ+) (hn : 5 ≤ (n : ℕ)) (x y : ℝ) (hx : x ∈ upperKA) (hy : y ∈ upperKA) :
    upperModel (((n : ℕ) : ℝ) + x + y) := by
  have hxb := upper_KA_bounds x hx
  have hyb := upper_KA_bounds y hy
  obtain ⟨l, hl, rfl⟩ := hx
  obtain ⟨r, hr, rfl⟩ := hy
  obtain ⟨hN, hc⟩ := upper_large_data n hn l r hl hr
  exact ⟨upperCentral n l r, 16 / 3, (n : ℕ), hN, hc,
    upper_large_margin n hn _ _ hxb hyb, upper_large_noncentral n hn l r hl hr⟩
