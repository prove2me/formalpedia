-- Prove2me | solution 1 for Freiman.lower_bridge_good
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:31.967419+00:00
-- url     : https://prove2.me/submissions/e5f05c9d-4ce6-49b4-ba39-71e8f4e95814

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_facts
import Theorems.Thm_Freiman_lower_bridge_endpoint_application
import Theorems.Thm_Freiman_lower_bridge_word_states
import Theorems.Thm_Freiman_lower_bridge_fork_geometry
import Theorems.Thm_Freiman_lower_bridge_chain_contacts
import Theorems.Thm_Freiman_lower_bridge_strip_bounds
import Theorems.Thm_Freiman_lower_bridge_interval_chain_cover
import Theorems.Thm_Freiman_lower_bridge_cover_order
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order

open Freiman

theorem solution (c : LowerBridgeCase) (n : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c ≠ .C) : lowerBridgeGood (lowerBridgeFamily c) n := by
  have h := Freiman.lower_bridge_facts c n 0 hc
  have he := Freiman.lower_bridge_endpoint_application c n 0 hc h
  intro t ht
  obtain ⟨d,hd,htd⟩ := Freiman.lower_bridge_interval_chain_cover _ _
    (Freiman.lower_bridge_cover_order c n hc hf)
    (Freiman.lower_bridge_chain_contacts c n hc hf h he Freiman.lowerEarlyTerminal_endpoint_order) t
    (Freiman.lower_bridge_strip_bounds c n hc hf h he t ht)
  have hs := Freiman.lower_bridge_word_states c n hc hf d hd
  exact ⟨d,hd,hs.1,Freiman.lower_bridge_fork_geometry c n hc hf h he Freiman.lowerEarlyTerminal_endpoint_order d hd,htd,hs.2⟩
