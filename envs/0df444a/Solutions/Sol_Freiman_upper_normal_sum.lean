-- Prove2me | solution 1 for Freiman.upper_normal_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:35:50.57833+00:00
-- url     : https://prove2.me/submissions/d4a18195-d8c2-4dcf-9f76-ccb910b99c78

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_path_exists
import Theorems.Thm_Freiman_upper_path_shrinks
import Theorems.Thm_Freiman_upper_path_limit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S) (mT : upperMesh T) (mS : upperMesh S) :
    upperDerived (T []) (S []) ⊆ upperSumSet (upperTreeSet T) (upperTreeSet S) := by
  intro z hz
  obtain ⟨u, v, hp⟩ := upper_path_exists T S hT hS z hz
  exact upper_path_limit T S hT hS mT mS u v z hp
    (upper_path_shrinks T S hT hS mT mS u v z hp)
