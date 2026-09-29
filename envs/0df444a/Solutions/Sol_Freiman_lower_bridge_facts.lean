-- Prove2me | solution 1 for Freiman.lower_bridge_facts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:31.905985+00:00
-- url     : https://prove2.me/submissions/00b43a04-289e-48ab-a02e-868cb340afff

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_parameter_box
import Theorems.Thm_Freiman_lower_bridge_matrix_link
import Theorems.Thm_Freiman_lower_bridge_numeric
import Theorems.Thm_Freiman_lower_bridge_width_transfer
import Theorems.Thm_Freiman_lower_bridge_aux_transfer
import Theorems.Thm_Freiman_lower_bridge_survivor_transfer
import Theorems.Thm_Freiman_lower_bridge_contact_transfer
import Theorems.Thm_Freiman_lower_initial_word_fraction

open Freiman

theorem solution (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) : lowerBridgeFacts c n k := by
  have hm := Freiman.lower_bridge_matrix_link c n k hc
  have hn := Freiman.lower_bridge_numeric c (lowerInitialX n) (lowerInitialY k) (Freiman.lower_bridge_parameter_box n k)
  have hw := Freiman.lower_bridge_width_transfer Freiman.lower_initial_word_fraction c n k hc hm hn
  intro r hr
  by_cases h1 : r.kind = .width
  · exact hw r hr h1
  by_cases h2 : r.kind = .auxiliary
  · exact Freiman.lower_bridge_aux_transfer Freiman.lower_initial_word_fraction c n k hc hm hn hw r hr h2
  by_cases h3 : r.kind = .h7 ∨ r.kind = .notA9
  · exact Freiman.lower_bridge_survivor_transfer Freiman.lower_initial_word_fraction c n k hc hm hn hw r hr h3
  exact Freiman.lower_bridge_contact_transfer Freiman.lower_initial_word_fraction c n k hc hm hn r hr ⟨h1,h2,fun h => h3 (Or.inl h),fun h => h3 (Or.inr h)⟩
