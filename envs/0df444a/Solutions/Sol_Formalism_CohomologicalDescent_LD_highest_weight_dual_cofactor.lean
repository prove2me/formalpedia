-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.highest_weight_dual_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:56.311789+00:00
-- url     : https://prove2.me/submissions/4673ac19-6fc8-4b53-997e-b8e615f651b2

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_highest_weight
import Theorems.Thm_Formalism_CohomologicalDescent_LD_highest_weight_dual_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (hM : ∀ a, ν a ≤ M) :
    genericDet ℤ r ^ (∑ a, ν a) * hw ℤ le_rfl (dualWt M ν) = genericDet ℤ r ^ M * cofMap r (hw ℤ le_rfl ν) := by
  have h0 : partialSumOfExponents ν 0 ≤ M := by
    unfold partialSumOfExponents
    split_ifs
    · exact hM _
    · exact Nat.zero_le _
  rw [highest_weight_dual_weight M ν hν hM, mul_left_comm, ← cofactor_highest_weight ν hν, ← mul_assoc, ← pow_add, Nat.sub_add_cancel h0]
end Formalism.CohomologicalDescent.LD
