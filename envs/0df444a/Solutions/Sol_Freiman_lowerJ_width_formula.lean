-- Prove2me | solution 1 for Freiman.lowerJ_width_formula
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:02.156659+00:00
-- url     : https://prove2.me/submissions/4c459787-75cf-4c66-b98e-a86ccb35310f

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_width_matrix
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lower_initial_matrix_bottom

open Freiman

theorem solution : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2)) := by
  exact Freiman.lowerJ_width_matrix Freiman.lower_initial_word_fraction Freiman.lower_initial_matrix_bottom
