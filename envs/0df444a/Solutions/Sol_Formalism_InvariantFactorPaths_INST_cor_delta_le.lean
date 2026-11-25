-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.cor_delta_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:19.44011+00:00
-- url     : https://prove2.me/submissions/85f483b8-fc43-431a-ae1a-198af73aeee5

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_L_div
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_gen
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_zpClosed_toAddSubgroup


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
theorem _root_.solution (hk : RowGlDiv) (hI : SwpInt) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (la : Fin r → ℤ) :
    DeltaLat p (GR p r ν) {h | (GR p r ν).IsHW la h ∧ h ∈ swappedDualWeyl p r n ν ∧
      h ∈ (IntPol p (Fin n × Fin r)).toAddSubgroup} ≤ (cor_L p hn ν).toAddSubgroup := by
  refine sInf_le ⟨?_, zpClosed_toAddSubgroup _, cor_L_div hk hn ν⟩
  rintro h ⟨a1, a2, a3⟩
  exact cor_gen hk hI hn ν hν la h a1 a2 a3
end Formalism.InvariantFactorPaths.INST
