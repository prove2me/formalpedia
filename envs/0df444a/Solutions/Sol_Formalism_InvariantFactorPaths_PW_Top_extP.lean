-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Top.extP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:20.307588+00:00
-- url     : https://prove2.me/submissions/9cd8a7ab-e62d-4bc9-b4ba-dca56c0015b2

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_extP_of
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homInv_of
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_intP_of
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_invariant_inverse_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_invariant_natural_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lattice_basis_polynomial
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_schurTrace_of
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_typeInt_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.InvariantFactorPaths.PW.Top
private theorem intP_statement : IntP := by
  have hInv : InvInv := invariant_inverse_holds
  exact intP_of (typeInt_of invariant_natural_holds (homInv_of hInv) (schurTrace_of hInv)) lattice_basis_polynomial
end Formalism.InvariantFactorPaths.PW.Top
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.PW.Top
namespace Formalism.InvariantFactorPaths.PW.Top
theorem _root_.solution : ExtP := extP_of intP_statement
end Formalism.InvariantFactorPaths.PW.Top
