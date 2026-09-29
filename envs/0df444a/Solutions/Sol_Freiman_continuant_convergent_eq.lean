-- Prove2me | solution 1 for Freiman.continuant_convergent_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:06.172678+00:00
-- url     : https://prove2.me/submissions/776c209b-e3bf-41b6-b707-ec84c3cb9d7c

import Definitions.Def_Freiman_continuants
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_prefixEval_zero

open Freiman

theorem solution (b : ℕ → ℕ+) (n : ℕ) :
    cfConvergent b n = (continuantP b n : ℝ) / continuantQ b n := by
  have h := prefixEval_mobius ((List.range n).map b) 0 (le_refl 0)
  simpa [prefixEval_zero, cfConvergent, continuantP, continuantQ] using h
