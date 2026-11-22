-- Prove2me | solution 1 for Csg.jointExpect_hide_throw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:02.943641+00:00
-- url     : https://prove2.me/submissions/37d92585-7783-405a-a8cc-7ac897a869ee

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
import Theorems.Thm_Csg_skirmishState_sum
import Theorems.Thm_Csg_homeWetSplit_home
import Theorems.Thm_Csg_homeWetSplit_wet
import Theorems.Thm_Csg_homeWetSplit_hide

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .hide .throw s').toReal * v s' =
      (4 / 5) * v .home + (1 / 5) * v .wet := by
  have h0 : (0:ℝ) ≤ (4 / 5 : ℝ) := by norm_num
  have h0' : (0:ℝ) ≤ 1 - (4 / 5 : ℝ) := by norm_num
  simp only [jointK, skirmishState_sum, homeWetSplit_home, homeWetSplit_wet, homeWetSplit_hide,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h0', ENNReal.toReal_zero]
  ring
end Csg
