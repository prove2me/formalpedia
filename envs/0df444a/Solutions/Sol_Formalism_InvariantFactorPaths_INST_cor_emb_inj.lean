-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.cor_emb_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:22.52936+00:00
-- url     : https://prove2.me/submissions/bd5da0c3-5afc-4f58-9c84-0e1d6cefb79b

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_emb_apply

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
theorem _root_.solution : Function.Injective (cor_emb p r n) := by
  intro x y h
  rw [cor_emb_apply, cor_emb_apply] at h
  exact MvPolynomial.map_injective _ (IsFractionRing.injective ℤ_[p] ℚ_[p]) ((swp ℚ_[p] r n).injective h)
end Formalism.InvariantFactorPaths.INST
