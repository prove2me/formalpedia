-- Prove2me | solution 1 for Freiman.upper_small_model
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:06.10089+00:00
-- url     : https://prove2.me/submissions/47a1e7de-5a22-49f5-8afe-1dd84f7ece69

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_KOne_bounds
import Theorems.Thm_Freiman_upper_small_data
import Theorems.Thm_Freiman_upper_small_noncentral
import Theorems.Thm_Freiman_upper_small_margin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (x y : ℝ) (hx : x ∈ upperKOne) (hy : y ∈ upperKOne) :
    upperModel (4 + x + y) := by
  have hxb := upper_KOne_bounds x hx
  have hyb := upper_KOne_bounds y hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨l, hl, hl0, rfl⟩ := hu
  obtain ⟨r, hr, hr0, rfl⟩ := hv
  obtain ⟨hN, hc⟩ := upper_small_data l r hl hl0 hr hr0
  exact ⟨upperCentral 4 (upperOne l) (upperOne r), upperSmallBound, 4, hN, hc,
    upper_small_margin _ _ hxb hyb, upper_small_noncentral l r hl hl0 hr hr0⟩
