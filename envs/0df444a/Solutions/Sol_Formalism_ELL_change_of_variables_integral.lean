-- Prove2me | solution 1 for Formalism.ELL.change_of_variables_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:43.15111+00:00
-- url     : https://prove2.me/submissions/90db509a-19dc-4ea0-a484-aad464ea5aef

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Change
import Theorems.Thm_Formalism_ELL_RootExponentBounds_change_of_variables_integral_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ELL Formalism.G
open Formalism Formalism.ELL
universe v
namespace Formalism.ELL
theorem _root_.solution : ChangeIntegral.{v} := Formalism.ELL.RootExponentBounds.change_of_variables_integral_of
end Formalism.ELL
