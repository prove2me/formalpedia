-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.partial_sequence_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:26.021785+00:00
-- url     : https://prove2.me/submissions/01bd8956-5921-4b7b-b246-253f12adead8

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (s : ℕ) : partialSumOfExponents ν (s + 1) ≤ partialSumOfExponents ν s := by
  unfold partialSumOfExponents
  by_cases h : s + 1 < r
  · rw [dif_pos h, dif_pos (by omega)]
    exact hν (Fin.le_def.mpr (by simp))
  · rw [dif_neg h]
    exact Nat.zero_le _
end Formalism.CohomologicalDescent.LD
