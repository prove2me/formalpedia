-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.cor_emb_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:19.473798+00:00
-- url     : https://prove2.me/submissions/6b639556-7cb6-44a1-b6c6-bfcced55b6a7

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_emb_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_hw_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (hn : n ≤ r) (ν : Fin n → ℕ) : cor_emb p r n (hw ℤ_[p] hn ν) = swappedHighestWeight p hn ν := by
  rw [cor_emb_apply, lclosedeq_hw_map, swappedHighestWeight]
end Formalism.InvariantFactorPaths.INST
