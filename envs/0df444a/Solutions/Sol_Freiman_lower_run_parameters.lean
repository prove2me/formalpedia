-- Prove2me | solution 1 for Freiman.lower_run_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:28.204391+00:00
-- url     : https://prove2.me/submissions/36cf18df-b11a-40f9-8524-b62b89147b04

import Theorems.Thm_Freiman_lower_run_parameter_transfer
import Theorems.Thm_Freiman_lower_run_tail_parameter
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerRunParameters p := by
  exact lower_run_parameter_transfer lower_run_tail_parameter t p hs hr
