-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.cor_L_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:15.597987+00:00
-- url     : https://prove2.me/submissions/4f3d3a51-cadb-4e4d-9f62-19b0ae48eeb4

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_emb_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_rowDiv_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylRowDivStable


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
theorem _root_.solution (hk : RowGlDiv) (hn : n ≤ r) (ν : Fin n → ℕ) :
    DivStable (GR p r ν).E (cor_L p hn ν).toAddSubgroup := by
  rintro a b hab k x ⟨y, hy, rfl⟩
  refine ⟨rowDiv ℤ_[p] a b k y, weylRowDivStable ℤ_[p] r n hn ν a b k y hy, ?_⟩
  rw [cor_emb_apply, cor_emb_apply, ← lclosedeq_rowDiv_map, hk p r n ν a b hab k]
end Formalism.InvariantFactorPaths.INST
