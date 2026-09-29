-- Prove2me | solution 1 for Freiman.lower_run_parity_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:02.421052+00:00
-- url     : https://prove2.me/submissions/29912a81-cff3-42e7-9129-81c042bf5fc9

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_width_formula
import Theorems.Thm_Freiman_lowerJ_offered_domain
import Theorems.Thm_Freiman_lowerJ_contact_threshold
import Theorems.Thm_Freiman_lower_initial_word_fraction
import Theorems.Thm_Freiman_lowerJ_signs
import Theorems.Thm_Freiman_lower_run_parameters
import Theorems.Thm_Freiman_lowerJ_inner_order
import Theorems.Thm_Freiman_lowerJ_first_cross
import Theorems.Thm_Freiman_lowerJ_reverse_cross
import Theorems.Thm_Freiman_lowerJ_inner_intersection
import Theorems.Thm_Freiman_lowerJ_inner_contained

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) :
    ∀ k : ℕ, 0 < k → (lowerCover (lowerRunPair p k) ∩ lowerCover (lowerRunPair p (k+2))).Nonempty := by
  have hd := Freiman.lowerJ_offered_domain Freiman.lowerJ_width_formula t p hs hr
  have hb := Freiman.lower_run_parameters t p hs hr
  intro k hk
  have hk2 : 0 < k+2 := by omega
  have hq := lt_trans hd.2.2.2 (Freiman.lowerJ_contact_threshold _ _ hd.1 hd.2.1 k hk)
  have h := Freiman.lowerJ_inner_intersection p k
    (Freiman.lowerJ_inner_order Freiman.lowerJ_signs t p hs hr k hk)
    (Freiman.lowerJ_inner_order Freiman.lowerJ_signs t p hs hr (k+2) hk2)
    (Freiman.lowerJ_first_cross Freiman.lower_initial_word_fraction t p hs hr k hk hq)
    (Freiman.lowerJ_reverse_cross Freiman.lowerJ_signs t p hs hr k hk)
  obtain ⟨x,hx⟩ := h
  exact ⟨x,Freiman.lowerJ_inner_contained t p hs hr k hk hb hx.1,
    Freiman.lowerJ_inner_contained t p hs hr (k+2) hk2 hb hx.2⟩
