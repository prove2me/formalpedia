-- Prove2me | solution 1 for Freiman.lower_bridge_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:08:20.397364+00:00
-- url     : https://prove2.me/submissions/d4e76f3d-f111-44e2-bab8-370ab0c737a3

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_rectangle_valid
import Theorems.Thm_Freiman_cert_bernstein_positive
import Theorems.Thm_Freiman_cert_bernstein_reconstruction
import Theorems.Thm_Freiman_cert_field_lower_bound

open Freiman

theorem solution (r : LowerBridgeRecord) (hr : lowerBridgeChecked r) (x y : ℝ) (hxy : certRectangleMem lowerBridgeRectangle x y) : 0 < certPolyEval r.polynomial x y := by
  rw [Freiman.cert_bernstein_reconstruction _ _ Freiman.lower_bridge_rectangle_valid]
  apply Freiman.cert_bernstein_positive _ _ _ _ Freiman.lower_bridge_rectangle_valid hxy
  intro i j
  have h := Freiman.cert_field_lower_bound (certBernsteinCoefficients r.polynomial lowerBridgeRectangle i j)
  have hp : (0:ℝ) < (certFieldLower (certBernsteinCoefficients r.polynomial lowerBridgeRectangle i j):ℝ) := by exact_mod_cast hr i j
  exact lt_of_lt_of_le hp h
