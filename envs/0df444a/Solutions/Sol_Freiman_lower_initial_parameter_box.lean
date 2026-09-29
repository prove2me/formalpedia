-- Prove2me | solution 1 for Freiman.lower_initial_parameter_box
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:29.622329+00:00
-- url     : https://prove2.me/submissions/6ed467fa-0814-4f61-9232-97bc69d8d54c

import Theorems.Thm_Freiman_lower_initial_period_ratio
import Theorems.Thm_Freiman_lower_initial_run_ratio
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (n k p : ℕ) : lowerInitialBox (lowerInitialX n) (lowerInitialY k) (lowerInitialY p) := by
  have hx := lower_initial_period_ratio n
  exact ⟨⟨hx.1,hx.2.2⟩,lower_initial_run_ratio k,lower_initial_run_ratio p⟩
