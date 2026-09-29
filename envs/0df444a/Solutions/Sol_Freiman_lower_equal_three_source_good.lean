-- Prove2me | solution 1 for Freiman.lower_equal_three_source_good
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:18.557293+00:00
-- url     : https://prove2.me/submissions/5e5a5c70-b457-4e30-a65f-54d8e1d23c55

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_width_formula
import Theorems.Thm_Freiman_lowerJ_equal_constants
import Theorems.Thm_Freiman_lowerJ_polynomials
import Theorems.Thm_Freiman_lowerJ_equal_Q
import Theorems.Thm_Freiman_lowerJ_equal_contact
import Theorems.Thm_Freiman_lowerJ_two_width_scalar
import Theorems.Thm_Freiman_lowerJ_equal_child_widths
import Theorems.Thm_Freiman_lower_auxiliary_width
import Theorems.Thm_Freiman_lowerJ_equal_endpoints
import Theorems.Thm_Freiman_lowerJ_equal_intersection

open Freiman

theorem solution (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p)
    (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p)
    (hwide : lowerWidth p.2 ≤ lowerWidth p.1)
    (hratio : lowerWidth p.1 < (19/5 : ℝ)*lowerWidth p.2) : lowerSourceGood p := by
  have hq := Freiman.lowerJ_equal_Q Freiman.lowerJ_width_formula Freiman.lowerJ_equal_constants Freiman.lowerJ_polynomials p ha hp hl hr hb hwide hratio
  have hc := Freiman.lowerJ_equal_contact Freiman.lowerJ_width_formula Freiman.lowerJ_equal_constants p ha hp hl hr hb hwide hratio hq
  have hw := Freiman.lowerJ_equal_child_widths Freiman.lowerJ_width_formula Freiman.lowerJ_two_width_scalar p ha hp hl hr hb hwide hratio
  have he := Freiman.lowerJ_equal_endpoints Freiman.lower_auxiliary_width p ha hp hl hr hb hwide hratio hc hw
  exact Freiman.lowerJ_equal_intersection Freiman.lowerJ_equal_constants p ha hp hl hr hb hwide hratio hc he
