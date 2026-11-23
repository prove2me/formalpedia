-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.ann_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:25.252484+00:00
-- url     : https://prove2.me/submissions/41b9f352-43ce-4c1c-af2f-826fd8f9ea27

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
theorem _root_.solution {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) : ann hL t ≠ ⊥ := by
  obtain ⟨n, hn, hnt⟩ := hL.2 t
  intro h
  have h1 : (n : 𝓞 (maximalRealSubfield E)) ∈ ann hL t := by
    rw [mem_ann, map_natCast]; exact hnt
  rw [h, Ideal.mem_bot] at h1
  have : n = 0 := by exact_mod_cast h1
  omega
end Formalism.FourierDecayAlt.P.S6x6
