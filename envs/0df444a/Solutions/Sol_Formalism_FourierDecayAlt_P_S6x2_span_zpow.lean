-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.span_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:24.60638+00:00
-- url     : https://prove2.me/submissions/4e343fb7-2282-4a66-8287-68f0ffb49377

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dd_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_span_le_of_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dd_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (c : E) (ν : ℤ) (hc : c ∈ dd E ^ ν.natAbs) :
    FractionalIdeal.spanSingleton (𝓞 E)⁰ c * dd E ^ ν ≤ 1 ∧
      FractionalIdeal.spanSingleton (𝓞 E)⁰ c ≤ dd E ^ ν := by
  have hC := span_le_of_mem E _ c hc
  have hD : dd E ^ ν.natAbs ≤ 1 := pow_le_one' (dd_le_one E) _
  have hD0 : dd E ^ ν.natAbs ≠ 0 := pow_ne_zero _ (dd_ne_zero E)
  rcases Int.natAbs_eq ν with h | h
  · have e : dd E ^ ν = dd E ^ ν.natAbs := by conv_lhs => rw [h, zpow_natCast]
    rw [e]
    exact ⟨(mul_le_mul' (hC.trans hD) hD).trans (by rw [one_mul]), hC⟩
  · have e : dd E ^ ν = (dd E ^ ν.natAbs)⁻¹ := by conv_lhs => rw [h, zpow_neg, zpow_natCast]
    rw [e]
    refine ⟨(mul_le_mul' hC le_rfl).trans (by rw [mul_inv_cancel₀ hD0]), (hC.trans hD).trans ?_⟩
    calc (1 : FI E) = dd E ^ ν.natAbs * (dd E ^ ν.natAbs)⁻¹ := (mul_inv_cancel₀ hD0).symm
      _ ≤ 1 * (dd E ^ ν.natAbs)⁻¹ := mul_le_mul' hD le_rfl
      _ = _ := one_mul _
end Formalism.FourierDecayAlt.P.S6x2
