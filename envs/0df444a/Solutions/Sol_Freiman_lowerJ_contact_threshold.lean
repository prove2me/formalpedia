-- Prove2me | solution 1 for Freiman.lowerJ_contact_threshold
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:02.413644+00:00
-- url     : https://prove2.me/submissions/199ccfc7-83b6-42da-94ac-037f9f2300f1

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_polynomials
import Theorems.Thm_Freiman_lowerJ_signs
import Theorems.Thm_Freiman_lower_run_tail_parameter
import Theorems.Thm_Freiman_lowerJ_contact_factor
import Theorems.Thm_Freiman_lowerJ_contact_iterate_box
import Theorems.Thm_Freiman_lowerJ_contact_one
import Theorems.Thm_Freiman_lowerJ_contact_bulk

open Freiman

theorem solution (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) (k : ℕ) (hk : 0 < k) : lowerJHStar r s < lowerJHK k r s := by
  have hp := Freiman.lowerJ_polynomials r s hr hs
  by_cases h : k=1
  · rw [h,Freiman.lowerJ_contact_one]
    exact hp.1
  have hk2 : 2 ≤ k := by omega
  exact lt_trans hp.2.1 (Freiman.lowerJ_contact_bulk r s hr hs k hk2
    (Freiman.lowerJ_contact_factor Freiman.lowerJ_signs _ (Freiman.lower_run_tail_parameter k hk))
    (Freiman.lowerJ_contact_iterate_box Freiman.lowerJ_signs k hk2))
