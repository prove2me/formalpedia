-- Prove2me | solution 2 for Freiman.lower_run_goodness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:22:41.041982+00:00
-- url     : https://prove2.me/submissions/0f92195f-1911-4a0d-88a4-a0188895894d

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_equal_three_good
import Theorems.Thm_Freiman_lower_run_parameters
import Theorems.Thm_Freiman_lower_run_goodness_transfer

open Freiman

-- `lower_run_goodness_transfer` proves goodness of every `lowerRunPair p k` from two extra
-- inputs beyond the state hypotheses: the per-core goodness criterion `hg` (which is
-- exactly `lower_equal_three_good`) and `lowerRunParameters p` (supplied by the Proved
-- `lower_run_parameters`).
theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) :
    ∀ k : ℕ, 0 < k → lowerGood (lowerRunPair p k) :=
  lower_run_goodness_transfer lower_equal_three_good t p hs hr
    (lower_run_parameters t p hs hr)
