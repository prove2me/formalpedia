-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.mem_of_forall_locAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:38.211994+00:00
-- url     : https://prove2.me/submissions/9ef2eac9-25a3-4b29-a188-e3e7ca108b68

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_mem_ann

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
theorem _root_.solution {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E)
    (ht : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ locAt E P L) : t ∈ L := by
  by_contra hcon
  have hI : ann hL t ≠ ⊤ := by
    intro h
    have h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ ann hL t := h ▸ Submodule.mem_top
    rw [mem_ann] at h1
    apply hcon
    simpa using h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨a, ha, hat⟩ := ht M hM
  exact ha (hIM hat)
end Formalism.FourierDecayAlt.P.S6x6
