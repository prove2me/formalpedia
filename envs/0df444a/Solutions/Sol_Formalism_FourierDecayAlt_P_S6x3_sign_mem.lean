-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.sign_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:45.05841+00:00
-- url     : https://prove2.me/submissions/71f55336-6584-4a6d-bee0-bffbd36438a1

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mul_mem_FI

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
theorem _root_.solution (A : FI E) (s : ℕ) (t : E) (ht : t ∈ A) : (-1) ^ s * t ∈ A := by
  have := mul_mem_FI E A ((-1) ^ s) t ht
  simpa using this
end Formalism.FourierDecayAlt.P.S6x3
