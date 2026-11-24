-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.exponent_arithmetic_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:42.796256+00:00
-- url     : https://prove2.me/submissions/e26cfc65-3d30-49a6-ac3e-63f5d9d28bdf

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eArith_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : EArith := by
  intro s ka β c h1 h2 h3
  have h4 := eArith_ge s ka β c h1 h2
  have h5 : (1 : ℤ) ≤ ∑ a ∈ range s, (β a : ℤ) := by exact_mod_cast h3
  linarith
end Formalism.InvariantFactorPaths.L4
