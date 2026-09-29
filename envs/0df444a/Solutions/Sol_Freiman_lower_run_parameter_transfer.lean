-- Prove2me | solution 1 for Freiman.lower_run_parameter_transfer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:02.290463+00:00
-- url     : https://prove2.me/submissions/63262f25-6883-4bea-ae08-b14ee0696d55

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_width_formula
import Theorems.Thm_Freiman_lowerJ_signs
import Theorems.Thm_Freiman_lowerJ_offered_domain
import Theorems.Thm_Freiman_lowerJ_append_parameters
import Theorems.Thm_Freiman_lowerJ_iterate_box
import Theorems.Thm_Freiman_lowerJ_Q_box
import Theorems.Thm_Freiman_lowerJ_width_parameters

open Freiman

theorem solution (htau : ∀ k : ℕ, 0 < k → (3/10 : ℝ) ≤ finiteCF (List.replicate k (3 : ℕ+)) ∧ finiteCF (List.replicate k (3 : ℕ+)) ≤ (1/3 : ℝ))
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerRunParameters p := by
  have hd := Freiman.lowerJ_offered_domain Freiman.lowerJ_width_formula t p hs hr
  intro k hk
  have hu := Freiman.lowerJ_append_parameters p k
  have hR : (1/4:ℝ) ≤ lowerRatio ((lowerNormalize p).1++List.replicate k 3) ∧ lowerRatio ((lowerNormalize p).1++List.replicate k 3) ≤ (1/3:ℝ) := by
    rw [hu.1]
    exact Freiman.lowerJ_iterate_box _ hd.1 k hk
  have hS : (1/4:ℝ) ≤ lowerRatio ((lowerNormalize p).2++List.replicate k 3) ∧ lowerRatio ((lowerNormalize p).2++List.replicate k 3) ≤ (1/3:ℝ) := by
    rw [hu.2.1]
    exact Freiman.lowerJ_iterate_box _ hd.2.1 k hk
  have hQ : (31/100:ℝ) < lowerScale ((lowerNormalize p).1++List.replicate k 3,(lowerNormalize p).2++List.replicate k 3) ∧ lowerScale ((lowerNormalize p).1++List.replicate k 3,(lowerNormalize p).2++List.replicate k 3) < (4/5:ℝ) := by
    rw [hu.2.2]
    exact Freiman.lowerJ_Q_box Freiman.lowerJ_signs _ _ _ _ hd (htau k hk)
  have hW := Freiman.lowerJ_width_parameters Freiman.lowerJ_width_formula Freiman.lowerJ_signs p k hu hR hS hQ
  exact ⟨hR.1,hR.2,hS.1,hS.2,hQ.1,hQ.2,hW.1,hW.2⟩
