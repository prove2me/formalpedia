-- Prove2me | solution 1 for ClauseBound.Part.exists_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:37:34.63556+00:00
-- url     : https://prove2.me/submissions/dacd0d6c-3be4-4997-b0c4-726a58f475d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Upper
import Definitions.Def_ClauseBound_Part_Lower
import Definitions.Def_ClauseBound_Part_Bounds
import Theorems.Thm_ClauseBound_Part_Bounds_logb_exp
import Theorems.Thm_ClauseBound_Part_Bounds_kappa_mul
import Theorems.Thm_ClauseBound_Part_exists_le_p
import Theorems.Thm_ClauseBound_Part_p_le_exp
import Theorems.Thm_ClauseBound_Part_p_pos


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open Bounds
namespace ClauseBound.Part
theorem _root_.solution : ∃ B C : ℝ, Partitions.Bounds B C := by
  obtain ⟨H, B, hH, hlow⟩ := exists_le_p
  refine ⟨B, max 0 (-Real.logb 2 H), fun E hE => ?_, fun E => ?_⟩
  · have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
    have hpos : 0 < H * Real.exp (cHR * Real.sqrt E) / (E : ℝ) ^ B := by positivity
    have h1 := Real.logb_le_logb_of_le one_lt_two hpos (hlow E hE)
    rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul hH.ne' (Real.exp_pos _).ne', logb_exp, Real.logb_pow] at h1
    have h2 : -Real.logb 2 H ≤ max 0 (-Real.logb 2 H) := le_max_right _ _
    rw [kappa_mul]
    linarith
  · have hp : (0 : ℝ) < p E := by exact_mod_cast p_pos E
    have h1 := Real.logb_le_logb_of_le one_lt_two hp (p_le_exp E)
    rw [logb_exp] at h1
    have h2 : (0 : ℝ) ≤ max 0 (-Real.logb 2 H) := le_max_left _ _
    rw [kappa_mul]
    linarith
end ClauseBound.Part
