-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.assembleLocal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:50.298919+00:00
-- url     : https://prove2.me/submissions/bd3598ed-444f-4a3c-b9e6-afa473e7d91d

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conj_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_ne_zero

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
theorem _root_.solution : AssembleLocal := by
  intro hC hS hTw hO hT hF hLG E _ _ _ g₁ g₂ h₁ h₂ ν s _
  have hg : 0 < g₁ * g₂ := Nat.mul_pos h₁.1.pos h₂.1.pos
  have hpd : PrimeToDifferent E (g₁ * g₂) := by
    have a := hS E g₁ h₁
    have b := hS E g₂ h₂
    unfold PrimeToDifferent at a b ⊢
    have : Ideal.span {((g₁ * g₂ : ℕ) : 𝓞 E)}
        = Ideal.span {(g₁ : 𝓞 E)} * Ideal.span {(g₂ : 𝓞 E)} := by
      rw [Ideal.span_singleton_mul_span_singleton]; push_cast; rfl
    rw [this]
    exact IsCoprime.mul_right a b
  refine ⟨fun P hP hgP => ?_, fun P hP hgP t => ?_, ?_⟩
  · ext t
    unfold perLat
    rw [hTw E _ _ s P hP.isPrime t, hO E _ 1 ν P hP.isPrime hgP, hO E _ 2 ν P hP.isPrime hgP]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    obtain ⟨a, ha, hat⟩ := h
    refine ⟨a, ha, ?_⟩
    change _ ∈ idl E (g₁ * g₂) 0 ν at hat
    show _ ∈ idl E (g₁ * g₂) 0 ν
    have hc := hC E (g₁ * g₂) 0 ν _ hat
    rw [map_mul, conj_real] at hc
    rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
    · have := (idl E (g₁ * g₂) 0 ν).coeToSubmodule.sub_mem hat hc
      have e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (t - 1 * complexConj E t)
          = algebraMap (𝓞 (maximalRealSubfield E)) E a * t
            - algebraMap (𝓞 (maximalRealSubfield E)) E a * complexConj E t := by ring
      rw [e]; exact this
    · have := (idl E (g₁ * g₂) 0 ν).coeToSubmodule.add_mem hat hc
      have e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (t - -1 * complexConj E t)
          = algebraMap (𝓞 (maximalRealSubfield E)) E a * t
            + algebraMap (𝓞 (maximalRealSubfield E)) E a * complexConj E t := by ring
      rw [e]; exact this
  · unfold perLat
    rw [hTw E _ _ s P hP.isPrime t, hT E _ 1 ν hg hpd P hP.isPrime hgP,
      hT E _ 2 ν hg hpd P hP.isPrime hgP]
  · exact hLG E _ (hF E _ _ s (idl_ne_zero E _ 2 ν hg) (idl_le E _ ν) (hC E _ 2 ν))
end Formalism.FourierDecayAlt.P.S6x2
