-- Prove2me | solution 1 for Freiman.lower_central_dominance
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:52.142785+00:00
-- url     : https://prove2.me/submissions/b92e9f87-a95e-4d39-95db-f25e32ee0c24

import Theorems.Thm_Freiman_lower_model_structure
import Theorems.Thm_Freiman_background_restricted
import Theorems.Thm_Freiman_background_constant_order
import Theorems.Thm_Freiman_lower_secondary_I3
import Theorems.Thm_Freiman_lower_secondary_I5
import Theorems.Thm_Freiman_lower_secondary_I6
import Theorems.Thm_Freiman_lower_secondary_I7
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (a : ℤ → ℕ+) (ha : LowerModel a) (i : ℤ) (hi : i ≠ 0) :
    localValue a i < (113195/25000 : ℝ) := by
  rcases lower_model_structure a ha with ⟨h4,h14,h41,_,hsecondary⟩
  by_cases h3 : (a i : ℕ) ≤ 3
  · exact lt_of_le_of_lt (background_restricted a h4 h14 h41 ha.1 i h3) background_constant_order.2.1
  · have h4i : (a i : ℕ) = 4 := by have := h4 i; omega
    rcases hsecondary i hi h4i with ⟨right,rfl,hc⟩
    rcases hc with hc | hc | hc | hc
    · exact lower_secondary_I3 a ha right hc
    · exact lower_secondary_I5 a ha right hc
    · exact lower_secondary_I6 a ha right hc
    · exact lower_secondary_I7 a ha right hc
