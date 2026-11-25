-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.cusp_centre_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:10:32.943079+00:00
-- url     : https://prove2.me/submissions/255f8403-14da-423e-b1d8-cecac7d57273

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_card_value_ne_run_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_card_lt_add_card_gt_add_card_eq

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
theorem _root_.solution : CuspCentre := by
  intro n p t lam c hpt hn hrun c₀ h
  by_contra hc
  have := card_value_ne_run_le n p t lam c hpt hrun c₀ hc
  have := card_lt_add_card_gt_add_card_eq n lam c₀
  omega
end Formalism.IrreducibleCountingLemmas.Z
