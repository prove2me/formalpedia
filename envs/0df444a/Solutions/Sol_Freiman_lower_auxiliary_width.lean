-- Prove2me | solution 1 for Freiman.lower_auxiliary_width
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:13.527045+00:00
-- url     : https://prove2.me/submissions/f990d3da-60ad-4091-8767-ac24bcb1958a

import Theorems.Thm_Freiman_prefixEval_append
import Theorems.Thm_Freiman_lower_beta_fixed
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (w : List ℕ+) : |prefixEval w lowerBeta - prefixEval (w ++ [1,3]) lowerAlpha| = lowerWidth (w ++ [1,3]) := by
  unfold lowerWidth
  rw [prefixEval_append w [1,3] lowerBeta, lower_beta_fixed]
