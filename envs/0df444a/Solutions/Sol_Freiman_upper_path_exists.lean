-- Prove2me | solution 1 for Freiman.upper_path_exists
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:35:50.477744+00:00
-- url     : https://prove2.me/submissions/1cd04a18-a649-4a22-8d29-11876d8324ad

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_one_deletion
import Theorems.Thm_Freiman_upper_choice_path
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S) (z : ℝ) (hz : z ∈ upperDerived (T []) (S [])) :
    ∃ u v : ℕ → List Bool, upperPath T S u v z := by
  exact upper_choice_path upper_one_deletion T S hT hS z hz
