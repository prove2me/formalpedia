-- Prove2me | solution 1 for Freiman.lower_initial_cover
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:55:39.048248+00:00
-- url     : https://prove2.me/submissions/ac892950-6699-49f0-be3f-55b55fb306e1

import Theorems.Thm_Freiman_lower_initial_connected
import Theorems.Thm_Freiman_lower_fixed_right_anchor
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution : Set.Icc cF (Real.sqrt 21) ⊆ lowerInitialSet := by
  intro t ht
  have hl : cF ∈ lowerInitialSet := Or.inl (Or.inl rfl)
  exact lower_initial_connected.ordConnected.out hl lower_fixed_right_anchor ht
