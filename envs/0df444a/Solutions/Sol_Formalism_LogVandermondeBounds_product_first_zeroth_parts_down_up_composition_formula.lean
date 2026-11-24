-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.down_up_composition_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:28.520848+00:00
-- url     : https://prove2.me/submissions/f26a335a-0f66-4f42-b357-c824ac4a6260

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_DU_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution : DualCompositionReformulated :=
  fun _ _ _ _ _ _ _ hr ψ x hx => DU_formula hr ψ x hx
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
