-- Prove2me | solution 1 for Freiman.lower_path_fairness_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:55:55.245464+00:00
-- url     : https://prove2.me/submissions/a35f08e7-9731-401a-8b24-373a42412e5a

import Definitions.Def_Freiman_lowerCertificates
import Theorems.Thm_Freiman_lower_path_fairness

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution
    (_hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p
      lowerWidth (q.1 ++ [2]) < lowerWidth q.2 ∧
      lowerWidth (q.1 ++ [3]) < lowerWidth q.2 ∧
      lowerWidth (q.1 ++ [1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2 ++ [1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    lowerWithinTwo (lowerPhysicalPath h) := by
  exact lower_path_fairness t h hh
