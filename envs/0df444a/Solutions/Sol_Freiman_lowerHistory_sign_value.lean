-- Prove2me | solution 1 for Freiman.lowerHistory_sign_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:35.091506+00:00
-- url     : https://prove2.me/submissions/77e53ac1-cc9d-4222-9f43-01d54067e182

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_sign_from_quadratic
import Theorems.Thm_Freiman_lowerHistory_quad_sign_value

open Freiman

theorem solution (z : CertField) :
    (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧ (0 < lowerHistorySign z ↔ 0 < certFieldVal z) := by
  exact lowerHistory_sign_from_quadratic lowerHistory_quad_sign_value z
