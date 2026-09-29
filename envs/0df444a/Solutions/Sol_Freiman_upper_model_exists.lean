-- Prove2me | solution 1 for Freiman.upper_model_exists
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:06.144384+00:00
-- url     : https://prove2.me/submissions/d8d16465-3643-41b8-acee-b07a925170ac

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_interval_cover
import Theorems.Thm_Freiman_upper_sum_A
import Theorems.Thm_Freiman_upper_sum_one
import Theorems.Thm_Freiman_upper_large_model
import Theorems.Thm_Freiman_upper_small_model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (t : ℝ) (ht : upperRayStart ≤ t) :
    upperModel t := by
  rcases upper_interval_cover t ht with ⟨n, hn, hz⟩ | hz
  · obtain ⟨x, hx, y, hy, hxy⟩ := upper_sum_A hz
    have h := upper_large_model n hn x y hx hy
    have heq : ((n : ℕ) : ℝ) + x + y = t := by linarith
    simpa only [heq] using h
  · obtain ⟨x, hx, y, hy, hxy⟩ := upper_sum_one hz
    have h := upper_small_model x y hx hy
    have heq : 4 + x + y = t := by linarith
    simpa only [heq] using h
