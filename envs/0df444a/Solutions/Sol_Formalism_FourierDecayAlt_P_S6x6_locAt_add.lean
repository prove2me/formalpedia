-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.locAt_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:20.191741+00:00
-- url     : https://prove2.me/submissions/38f9b945-5106-4c7d-962c-ede423cb0d2a

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
namespace Formalism.FourierDecayAlt.P.S6x6
theorem _root_.solution {L : Submodule ℤ E} (hL : IsFLattice E L)
    {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) {x y : E}
    (hx : x ∈ locAt E P L) (hy : y ∈ locAt E P L) : x + y ∈ locAt E P L := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  refine ⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩
  have h1 := hL.1 b _ hax
  have h2 := hL.1 a _ hby
  have h3 : algebraMap (𝓞 (maximalRealSubfield E)) E (a * b) * (x + y) =
      algebraMap (𝓞 (maximalRealSubfield E)) E b * (algebraMap (𝓞 (maximalRealSubfield E)) E a * x) +
      algebraMap (𝓞 (maximalRealSubfield E)) E a * (algebraMap (𝓞 (maximalRealSubfield E)) E b * y) := by
    rw [map_mul]; ring
  rw [h3]; exact L.add_mem h1 h2
end Formalism.FourierDecayAlt.P.S6x6
