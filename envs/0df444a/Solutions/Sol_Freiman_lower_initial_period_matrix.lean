-- Prove2me | solution 1 for Freiman.lower_initial_period_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:29.456615+00:00
-- url     : https://prove2.me/submissions/a2c56e17-729a-41ce-9ff1-24d912bf3adb

import Theorems.Thm_Freiman_lower_initial_period_scaled_identity
import Theorems.Thm_Freiman_lower_initial_period_positive
import Theorems.Thm_Freiman_lower_initial_period_recurrence_matrix
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (n : ℕ) (hn : 0 < n) : lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n)) := by
  exact lower_initial_period_scaled_identity n hn (lower_initial_period_positive n hn) (lower_initial_period_recurrence_matrix n hn)
