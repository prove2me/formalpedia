-- Prove2me | solution 1 for Formalism.LatticeIndexTer.latBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:29.621562+00:00
-- url     : https://prove2.me/submissions/423b48ce-663b-4b6f-8f47-2da58af3d392

import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Theorems.Thm_Formalism_LatticeIndexTer_lattice_has_basis


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
theorem _root_.solution : LatBasis := lattice_has_basis
end Formalism.LatticeIndexTer
