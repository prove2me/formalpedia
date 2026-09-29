-- Prove2me | solution 1 for Freiman.lower_bridge_matrix_link
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:08:18.290229+00:00
-- url     : https://prove2.me/submissions/e3fb06e8-1970-4803-ad2e-2eb16ca8ee9b

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_initial_family_matrix

open Freiman

theorem solution (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) : lowerInitialSeamLink (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0 := by
  exact Freiman.lower_initial_family_matrix (lowerBridgeSeamCase c) n (lowerBridgeK c k) 0 hc
