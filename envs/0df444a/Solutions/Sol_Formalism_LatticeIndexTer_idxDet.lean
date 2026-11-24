-- Prove2me | solution 1 for Formalism.LatticeIndexTer.idxDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:56.672678+00:00
-- url     : https://prove2.me/submissions/f66b75f3-701f-4552-a425-303c335b4bed

import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Theorems.Thm_Formalism_LatticeIndexTer_lattice_index_eq_det_valuation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeIndexTer
namespace Formalism.LatticeIndexTer
theorem _root_.solution : IdxDet := lattice_index_eq_det_valuation
end Formalism.LatticeIndexTer
