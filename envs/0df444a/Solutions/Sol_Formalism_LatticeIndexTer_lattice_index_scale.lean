-- Prove2me | solution 1 for Formalism.LatticeIndexTer.lattice_index_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:21.278279+00:00
-- url     : https://prove2.me/submissions/40f401a5-8006-4cba-a93d-a786c5884b8a

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Formalism_LatticeIndexTer_idxScale_of
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_lattice_span_of_basis

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
theorem _root_.solution : IdxScale := idxScale_of LatticeIndexDeterminant.lattice_span_of_basis
end Formalism.LatticeIndexTer
