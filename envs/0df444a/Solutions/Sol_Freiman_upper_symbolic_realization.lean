-- Prove2me | solution 1 for Freiman.upper_symbolic_realization
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:06.372072+00:00
-- url     : https://prove2.me/submissions/3056eb27-74a4-435a-9e8e-81aa47cbfe29

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_model_exists
import Theorems.Thm_Freiman_upper_model_symbolic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (t : ℝ) (ht : upperRayStart ≤ t) :
    t ∈ symbolicLagrangeSpectrum := by
  exact upper_model_symbolic t ht (upper_model_exists t ht)
