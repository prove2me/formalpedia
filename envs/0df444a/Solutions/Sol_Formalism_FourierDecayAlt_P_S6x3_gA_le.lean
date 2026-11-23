-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.gA_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:19.077843+00:00
-- url     : https://prove2.me/submissions/fe8a6f0d-ae42-4807-9c32-d00c19132bc4

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mul_mem_FI
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_gA

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
theorem _root_.solution (A : FI E) (g : ℕ) (x : E)
    (hx : x ∈ A * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E)) : x ∈ A := by
  obtain ⟨a, ha, rfl⟩ := (mem_gA E A g x).mp hx
  have := mul_mem_FI E A (g : 𝓞 E) a ha
  simpa using this
end Formalism.FourierDecayAlt.P.S6x3
