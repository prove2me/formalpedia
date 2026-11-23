-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.exists_delta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:31.189154+00:00
-- url     : https://prove2.me/submissions/6f736c27-e1ae-4da8-8d06-b56da9a291fa

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
theorem _root_.solution : ∃ δ : 𝓞 E, (δ : E) ≠ 0 ∧ complexConj E δ = -(δ : E) := by
  by_contra h
  push Not at h
  have hfix : ∀ a : 𝓞 E, complexConj E a = a := by
    intro a
    by_contra hne
    refine h (a - ringOfIntegersComplexConj E a) ?_ ?_
    · intro h0
      apply hne
      have : (a : E) - complexConj E a = 0 := h0
      linear_combination -this
    · have : ((a - ringOfIntegersComplexConj E a : 𝓞 E) : E) = (a : E) - complexConj E a := rfl
      rw [this, map_sub, complexConj_apply_apply]
      ring
  apply complexConj_ne_one E
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, hfix, hfix]
  rfl
end Formalism.FourierDecayAlt.P.S6x3
