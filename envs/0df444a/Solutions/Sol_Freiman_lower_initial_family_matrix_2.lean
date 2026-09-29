-- Prove2me | solution 2 for Freiman.lower_initial_family_matrix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:14:43.156381+00:00
-- url     : https://prove2.me/submissions/b3c6f96e-5250-4d3b-8c67-1e5ff744cbff

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_initial_period_matrix
import Theorems.Thm_Freiman_lower_initial_period_positive
import Theorems.Thm_Freiman_lower_initial_run_positive
import Theorems.Thm_Freiman_lower_initial_run_matrix
import Theorems.Thm_Freiman_lower_initial_family_normalization
import Theorems.Thm_Freiman_lower_initial_family_matrix_transfer

open Freiman
open scoped BigOperators

-- `lower_initial_family_matrix_transfer` isolates the five matrix/positivity inputs of
-- the family seam link; each is an existing node, so the link follows immediately.
theorem solution (c : LowerInitialSeamCase) (n k p : ℕ)
    (hc : lowerInitialSeamZero c = decide (n = 0)) : lowerInitialSeamLink c n k p :=
  lower_initial_family_matrix_transfer
    (fun n hn => lower_initial_period_matrix n hn)
    (fun n hn => lower_initial_period_positive n hn)
    (fun k => lower_initial_run_positive k)
    (fun k => lower_initial_run_matrix k)
    (fun f n k p hf => lower_initial_family_normalization f n k p hf)
    c n k p hc
