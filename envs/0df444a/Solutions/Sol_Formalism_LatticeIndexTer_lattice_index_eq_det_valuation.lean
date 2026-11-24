-- Prove2me | solution 1 for Formalism.LatticeIndexTer.lattice_index_eq_det_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:31.651018+00:00
-- url     : https://prove2.me/submissions/7c2b3529-9339-4b1d-b56d-1a406984dbef

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_idxDet_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
namespace Formalism.LatticeIndexTer
theorem _root_.solution : IdxDet := by
  intro O K X Y ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bX bY f a b ha hb h
  exact LatticeIndexDeterminant.idxDet_core bX bY f a b ha hb h
end Formalism.LatticeIndexTer
