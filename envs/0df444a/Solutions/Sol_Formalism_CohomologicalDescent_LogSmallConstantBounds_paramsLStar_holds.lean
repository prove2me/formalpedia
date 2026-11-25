-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLStar_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:33.754056+00:00
-- url     : https://prove2.me/submissions/be08fb49-7501-4eab-8ff8-f873e97e3320

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_eq_div
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJ_eq_div
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJDenom_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJDenom_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_seven_lt_lstar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
private theorem div_le_div_of_le_of_pos {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hcb : c ≤ b) :
    a / b ≤ a / c := by
  calc a / b = a * (1 / b) := by ring
    _ ≤ a * (1 / c) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hc hcb) ha
    _ = a / c := by ring
private theorem lJDenom_le_lstarDenom {P : Par} (H : P.Hyp) (G : P.Large) :
    indexDenominator P ≤ lstarDenom P := by
  have nb := natBounds H
  have hL := G.L_ge
  have hS := H.S_nonneg
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hN : (P.k : ℝ) ≤ P.N + P.t := by
    unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.N
    have : 0 ≤ (P.m : ℝ) * (P.t + 1) := by positivity
    linarith
  have h4 : (4 : ℝ) ≤ P.t * P.L := by nlinarith [nb.t6]
  have h0 : 0 ≤ (P.k : ℝ) * P.t * P.L := mul_nonneg (mul_nonneg hk0 ht0) (by linarith)
  have e1 := mul_le_mul_of_nonneg_left h4 h0
  have hkn : (P.k : ℝ) ≤ P.n * (P.N + P.t) := by
    nlinarith [mul_nonneg (sub_nonneg.2 nb.n1) (le_trans hk0 hN)]
  have e2 := mul_le_mul_of_nonneg_left hkn (by positivity : (0 : ℝ) ≤ (P.t : ℝ) ^ 2 * P.L ^ 2)
  have e3 : 0 ≤ (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + P.t + P.L) :=
    mul_nonneg (by positivity) (by linarith)
  have e4 := lJDenom_le H G
  unfold lstarDenom
  nlinarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : Elem_b := by
  intro P H G
  have hJ := lJDenom_pos H G
  have hb := b_pos' P
  have nb := natBounds H
  have hL := G.L_ge
  have h7 := seven_lt_lstar H G
  refine ⟨?_, by nlinarith⟩
  have key := lJDenom_le_lstarDenom H G
  rw [lstar_eq_div, lJ_eq_div]
  calc P.L * ((P.m : ℝ) * P.b / lstarDenom P) = (P.m : ℝ) * P.b * P.L / lstarDenom P := by ring
    _ ≤ (P.m : ℝ) * P.b * P.L / indexDenominator P :=
        div_le_div_of_le_of_pos
          (mul_nonneg (mul_nonneg (by linarith [nb.m1]) hb.le) (by linarith)) hJ key
end Formalism.CohomologicalDescent.LogSmallConstantBounds
