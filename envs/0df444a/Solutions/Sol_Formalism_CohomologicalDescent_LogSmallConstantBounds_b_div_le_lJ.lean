-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.b_div_le_lJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:32.973904+00:00
-- url     : https://prove2.me/submissions/db5a4a96-b5d0-4702-92d7-0a946304494e

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJ_eq_div
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJDenom_pos
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJDenom_le
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
private theorem div_le_div_of_le_of_nonneg_right {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hc)
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) :
    P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) ≤ P.lJ := by
  have nb := natBounds H
  have hb := b_pos' P
  have hL := G.L_ge
  have hJ := lJDenom_pos H G
  have hkt : 0 < 4 * (P.k : ℝ) * (P.t : ℝ) :=
    mul_pos (mul_pos (by norm_num) (by linarith [nb.k1])) (by linarith [nb.t6])
  calc P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) ≤ (P.m : ℝ) * P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) :=
        div_le_div_of_le_of_nonneg_right (by nlinarith [nb.m1]) hkt.le
    _ = (P.m : ℝ) * P.b * P.L / (4 * (P.k : ℝ) * (P.t : ℝ) * P.L) :=
        (mul_div_mul_right _ _ (by linarith : P.L ≠ 0)).symm
    _ ≤ (P.m : ℝ) * P.b * P.L / indexDenominator P :=
        div_le_div_of_le_of_pos
          (mul_nonneg (mul_nonneg (by linarith [nb.m1]) hb.le) (by linarith)) hJ
          (lJDenom_le H G)
    _ = P.lJ := (lJ_eq_div P).symm
end Formalism.CohomologicalDescent.LogSmallConstantBounds
