-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.rk_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:22.185422+00:00
-- url     : https://prove2.me/submissions/f4975886-96e6-4445-8902-27489b03cf1b

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_rk_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_eig_add_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (A : FI E) (s : ℕ) : finrank ℤ (eig E A (s + 1)) = finrank ℤ (eig E A s) := by
  apply le_antisymm _ (rk_le E A s)
  have := rk_le E A (s + 1)
  rwa [eig_add_two] at this
end Formalism.FourierDecayAlt.P.S6x3
