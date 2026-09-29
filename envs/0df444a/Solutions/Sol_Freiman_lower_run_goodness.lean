-- Prove2me | solution 1 for Freiman.lower_run_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:28.35683+00:00
-- url     : https://prove2.me/submissions/09dee703-5e13-4761-b7d6-e699b4b93a20

import Theorems.Thm_Freiman_lower_run_goodness_transfer
import Theorems.Thm_Freiman_lower_equal_three_good
import Theorems.Thm_Freiman_lower_run_parameters
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) :
    ∀ k : ℕ, 0 < k → lowerGood (lowerRunPair p k) := by
  exact lower_run_goodness_transfer lower_equal_three_good t p hs hr (lower_run_parameters t p hs hr)
