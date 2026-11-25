-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsTop_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:05.693164+00:00
-- url     : https://prove2.me/submissions/20a66be7-f299-4383-9906-4237b98090b9

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_div_le_lJ

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
theorem _root_.solution : Elem_e := by
  intro P H G
  have nb := natBounds H
  have hc := b_div_le_lJ H G
  have hkt : 0 < 4 * (P.k : ℝ) * (P.t : ℝ) :=
    mul_pos (mul_pos (by norm_num) (by linarith [nb.k1])) (by linarith [nb.t6])
  have : 3 * P.b' < P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) := by
    rw [lt_div_iff₀ hkt]
    nlinarith [G.bb']
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
