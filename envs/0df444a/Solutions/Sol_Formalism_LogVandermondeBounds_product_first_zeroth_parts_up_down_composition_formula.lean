-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.up_down_composition_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:29:19.05366+00:00
-- url     : https://prove2.me/submissions/614ad7b5-f01a-495f-8f0b-62d801314b68

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_opU_eq_opD
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmP_eq_nmV
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
theorem _root_.solution : CompositionWithDual := by
  intro k _ _ _ r R _ hr φ f hf
  rw [← opU_eq_opD φ, opU_eq_opD (opU φ), nmP_eq_nmV]
  exact DU_formula hr φ f hf
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
