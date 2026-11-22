-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.mul_mem_FI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:28.388799+00:00
-- url     : https://prove2.me/submissions/d8436cea-173e-428c-85f3-92e508173ec4

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe

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
theorem _root_.solution (A : FI E) (z : 𝓞 E) (t : E) (ht : t ∈ A) : (z : E) * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem z ht
  rw [Algebra.smul_def] at this
  exact this
end Formalism.FourierDecayAlt.P.S6x3
