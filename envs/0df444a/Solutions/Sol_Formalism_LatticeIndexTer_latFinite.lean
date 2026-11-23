-- Prove2me | solution 1 for Formalism.LatticeIndexTer.latFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:40.487848+00:00
-- url     : https://prove2.me/submissions/65b7367c-1212-4808-89b4-62aaebec7034

import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Theorems.Thm_Formalism_LatticeIndexTer_lattice_quotient_finite


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
theorem _root_.solution : LatFinite := lattice_quotient_finite
end Formalism.LatticeIndexTer
