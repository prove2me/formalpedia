-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.swapped_highest_weight_isHW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:42:38.892726+00:00
-- url     : https://prove2.me/submissions/a781cae7-d78b-453f-93c4-8c5f17426c2d

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_weight_rowW
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRaise
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight


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
theorem _root_.solution (h1 : RowGlOne) (hw' : SwpWt) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    (GR p r ν).IsHW (fun a => (rowNu ν a : ℤ)) (swappedHighestWeight p hn ν) := by
  refine ⟨(hw' p r n ν _ _).mpr fun m hm a => ?_, fun a b hab => ?_⟩
  · have := hwRowWeight ℚ_[p] r n hn ν hν (mem_support_iff.mp hm)
    rw [← cor_weight_rowW, this]
  · rw [swappedHighestWeight, ← h1 p r n ν a b, hwRaise ℚ_[p] r n hn ν a b 1 hab le_rfl, map_zero]
end Formalism.InvariantFactorPaths.INST
