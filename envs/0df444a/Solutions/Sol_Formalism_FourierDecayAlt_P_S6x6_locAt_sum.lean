-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.locAt_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:04.210049+00:00
-- url     : https://prove2.me/submissions/1405c62c-e5fc-4550-a258-01c6fc547d9a

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_locAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_locAt_zero

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
    {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) {ι : Type*} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, f i ∈ locAt E P L) : ∑ i ∈ s, f i ∈ locAt E P L :=
  Finset.sum_induction f (fun x => x ∈ locAt E P L) (fun _ _ hx hy => locAt_add hL hP hx hy)
    (locAt_zero L hP) h
end Formalism.FourierDecayAlt.P.S6x6
