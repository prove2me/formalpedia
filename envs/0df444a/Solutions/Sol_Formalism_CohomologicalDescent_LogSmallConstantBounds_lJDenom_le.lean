-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.lJDenom_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:49:51.344717+00:00
-- url     : https://prove2.me/submissions/fdad8b43-3efd-47f9-8d91-8690f508d9cb

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_three_mul_h_pos_le

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
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) :
    indexDenominator P ≤ 4 * (P.k : ℝ) * (P.t : ℝ) * P.L := by
  have nb := natBounds H
  have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have a : (P.m : ℝ) + P.t ≤ 2 * P.t := by linarith [nb.mt, nb.m1]
  obtain ⟨c1, c2⟩ := log_three_mul_h_pos_le H G
  have e : ((P.m : ℝ) + P.t) * Real.log (3 * P.h) ≤ (2 * P.t) * (2 * P.L) :=
    mul_le_mul a c2 c1.le (by linarith [nb.t6])
  have := mul_le_mul_of_nonneg_left e hk
  unfold indexDenominator
  nlinarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
