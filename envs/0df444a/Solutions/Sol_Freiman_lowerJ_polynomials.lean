-- Prove2me | solution 1 for Freiman.lowerJ_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:02.17176+00:00
-- url     : https://prove2.me/submissions/8df49a69-1613-4df6-8b41-21c8397c8261

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_poly_positive
import Theorems.Thm_Freiman_lowerJ_poly_binding_0
import Theorems.Thm_Freiman_lowerJ_poly_binding_1
import Theorems.Thm_Freiman_lowerJ_poly_binding_2
import Theorems.Thm_Freiman_lowerJ_poly_binding_3

open Freiman

theorem solution (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : lowerJPolyFacts r s := by
  exact ⟨(Freiman.lowerJ_poly_binding_0 r s hr hs).mp (Freiman.lowerJ_poly_positive 0 r s hr hs),(Freiman.lowerJ_poly_binding_1 r s hr hs).mp (Freiman.lowerJ_poly_positive 1 r s hr hs),(Freiman.lowerJ_poly_binding_2 r s hr hs).mp (Freiman.lowerJ_poly_positive 2 r s hr hs),(Freiman.lowerJ_poly_binding_3 r s hr hs).mp (Freiman.lowerJ_poly_positive 3 r s hr hs)⟩
