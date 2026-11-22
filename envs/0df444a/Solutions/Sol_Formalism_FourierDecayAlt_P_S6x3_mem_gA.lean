-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.mem_gA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:54.829028+00:00
-- url     : https://prove2.me/submissions/a4c9b35f-f23a-4066-8254-e07640fd38fb

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
theorem _root_.solution (A : FI E) (g : ℕ) (x : E) :
    x ∈ A * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) ↔ ∃ a ∈ A, x = (g : E) * a := by
  rw [mul_comm, FractionalIdeal.mem_singleton_mul]
end Formalism.FourierDecayAlt.P.S6x3
