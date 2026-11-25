-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.slack_size_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:10.972821+00:00
-- url     : https://prove2.me/submissions/6eecef91-c4b7-4421-909f-6adde7565446

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_add_seven_le_h
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_le_lstarDenom
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstarDenom_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_eq_div
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsBasic_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLStar_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_seven_lt_lstar
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : SlackSize := by
  intro P H G
  have N := LogSmallConstantBounds.natBounds H
  have hD := LogSmallConstantBounds.le_lstarDenom H G
  have hDp := LogSmallConstantBounds.lstarDenom_pos H G
  have hb := LogSmallConstantBounds.b_pos' P
  have hL := G.L_ge
  have hls := LogSmallConstantBounds.lstar_pos H G
  have t6 := N.t6; have m1 := N.m1; have mt := N.mt
  have hr : P.b / P.lstar = LogSmallConstantBounds.lstarDenom P / (P.m : ℝ) := by
    rw [LogSmallConstantBounds.lstar_eq_div]; field_simp
  constructor
  · rw [hr, le_div_iff₀ (by linarith)]
    have hL2 : (16 : ℝ) ≤ P.L ^ 2 := by nlinarith
    have h1 : (P.t : ℝ) ^ 3 * 16 ≤ (P.t : ℝ) ^ 3 * P.L ^ 2 := by gcongr
    have h2 : 48 * (P.t : ℝ) ^ 2 * (P.m : ℝ) ≤ (P.t : ℝ) ^ 3 * 16 := by
      have : 0 ≤ (P.t : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  · intro l hl
    have hbE := LogSmallConstantBounds.paramsLStar_holds P H G
    have h0 := LogSmallConstantBounds.paramsBasic_holds P H G
    have h7 := LogSmallConstantBounds.seven_lt_lstar H G
    have hl1 : 3 * P.lstar ≤ (l : ℝ) - 1 := by nlinarith [hbE.1]
    have hl1p : 0 < (l : ℝ) - 1 := by linarith
    have hh : 0 ≤ P.h := by have := LogSmallConstantBounds.b_add_seven_le_h H; linarith
    have k1 : (P.kap l : ℝ) ≤ P.h / ((l : ℝ) - 1) := Nat.floor_le (by positivity)
    have k2 : P.h / ((l : ℝ) - 1) ≤ 2 * P.b / (3 * P.lstar) := by
      apply div_le_div₀ (by positivity) h0.2.2 (by positivity) hl1
    have k3 : 2 * P.b / (3 * P.lstar) = 2 / 3 * (P.b / P.lstar) := by field_simp
    linarith
end Formalism.CohomologicalDescent.WorkedExample
