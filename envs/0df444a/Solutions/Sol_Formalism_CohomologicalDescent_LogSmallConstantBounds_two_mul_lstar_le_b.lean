-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.two_mul_lstar_le_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:02.428124+00:00
-- url     : https://prove2.me/submissions/bed8a24a-9bc7-4765-ba7d-a945a705346e

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstar_eq_div
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_le_lstarDenom
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lstarDenom_pos

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) : 2 * P.lstar ≤ P.b := by
  have nb := natBounds H
  have hL := G.L_ge
  have hb := b_pos' P
  have hD := lstarDenom_pos H G
  have hle := le_lstarDenom H G
  have ht6 := nb.t6
  have ht2 : (36 : ℝ) ≤ (P.t : ℝ) ^ 2 := by nlinarith
  have hL2 : (16 : ℝ) ≤ P.L ^ 2 := by nlinarith
  have h36' := mul_le_mul ht2 hL2 (by norm_num) (by positivity)
  have h36 : (1 : ℝ) ≤ (P.t : ℝ) ^ 2 * P.L ^ 2 := by linarith
  have htt : (P.t : ℝ) ≤ (P.t : ℝ) ^ 3 * P.L ^ 2 := by
    have := mul_le_mul_of_nonneg_left h36 (by linarith : (0 : ℝ) ≤ P.t)
    nlinarith
  have hm : 2 * (P.m : ℝ) ≤ lstarDenom P := by linarith [nb.mt, nb.m1]
  rw [lstar_eq_div, mul_div_assoc', div_le_iff₀ hD]
  nlinarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
