-- Prove2me | solution 1 for Freiman.lowerJ_signs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:47.873154+00:00
-- url     : https://prove2.me/submissions/1429d946-1802-4735-93b9-dcc6714ac5a0

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_sign_binding
import Theorems.Thm_Freiman_lowerJ_sign_check
import Theorems.Thm_Freiman_cert_field_lower_bound

open Freiman

theorem solution : lowerJSignFacts := by
  intro i
  rw [← Freiman.lowerJ_sign_binding i]
  have h := Freiman.cert_field_lower_bound (lowerJSignFields i)
  have hp : (0:ℝ) < (certFieldLower (lowerJSignFields i):ℝ) := by exact_mod_cast Freiman.lowerJ_sign_check i
  exact lt_of_lt_of_le hp h
