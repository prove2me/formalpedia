-- Prove2me | solution 1 for CircuitLowerBound.not_sat_nil_clause
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:21:16.962223+00:00
-- url     : https://prove2.me/submissions/a0aec714-edb4-41df-ac5c-686d7e85238f

import Definitions.Def_CircuitLowerBoundStatement
import Mathlib.Tactic
set_option autoImplicit false

open ENP

theorem solution : ¬Sat [[]] := by
  rintro ⟨a, h⟩
  simpa using h [] (by simp)
