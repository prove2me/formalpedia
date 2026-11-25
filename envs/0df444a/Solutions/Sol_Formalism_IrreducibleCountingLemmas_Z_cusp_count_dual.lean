-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.cusp_count_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:17:14.4123+00:00
-- url     : https://prove2.me/submissions/a24247c7-6bcc-43ca-9e56-c562d703e968

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_cusp_count_symmetric

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
theorem _root_.solution : CuspCountDual := by
  intro n p t lam c hpt hn hrun c₀ i hi ⟨h1, h2⟩
  exact cusp_count_symmetric n p t lam c hpt hn hrun c₀ i hi (by omega)
end Formalism.IrreducibleCountingLemmas.Z
