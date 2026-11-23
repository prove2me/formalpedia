-- Prove2me | solution 1 for Formalism.FN.existsAdaptedBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:20.800798+00:00
-- url     : https://prove2.me/submissions/376dc512-d5c4-4842-8815-f9ebdec2c470

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_AdaptedBasis
import Theorems.Thm_Formalism_FN_AdaptedBasisExistence_adapted_basis_exists

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
namespace Formalism.FN
theorem _root_.solution : Formalism.FN.AdaptedBasis := Formalism.FN.AdaptedBasisExistence.adapted_basis_exists
end Formalism.FN
