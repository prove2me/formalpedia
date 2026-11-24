-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.fifth_factor_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:01:33.659731+00:00
-- url     : https://prove2.me/submissions/2752c053-7950-4928-9d60-288873a89ce8

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_factorOverLocalSubalgebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : FactorOverLocalSubalgebraMonic := by
  intro O _ _ X' _ T hT t c F s hF h1 h2
  obtain ⟨P, hP1, hP2, hP3⟩ := factorOverLocalSubalgebra O X' T hT t c F s h1 h2
  refine ⟨P, ?_, hP1, hP2, hP3⟩
  rw [hP1] at hF
  exact Monic.of_mul_monic_right ((monic_X_sub_C _).pow t) hF
end Formalism.IrreducibleCountingLemmas.Z
