-- Prove2me | solution 2 for Freiman.lower_path_fairness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:03:56.133886+00:00
-- url     : https://prove2.me/submissions/702afe9f-4709-4d12-98ce-8b845cdbe88a

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_forced_reflections
import Theorems.Thm_Freiman_lower_path_fairness_transfer

open Freiman

-- The unconditional fairness statement follows from the transfer lemma by supplying the
-- forced-reflections width comparisons.
theorem solution (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    lowerWithinTwo (lowerPhysicalPath h) :=
  lower_path_fairness_transfer
    (fun p hg hb => lower_forced_reflections p hg hb) t h hh
