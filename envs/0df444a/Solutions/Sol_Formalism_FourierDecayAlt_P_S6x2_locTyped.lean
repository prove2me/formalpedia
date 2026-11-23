-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.locTyped
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:43.331085+00:00
-- url     : https://prove2.me/submissions/024a5357-56ec-48de-9f09-4245625a228d

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_exists_real_mem_dd
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_span_zpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_pow_mem_pow

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
theorem _root_.solution : LocTyped := by
  intro E _ _ _ g k ν hg hpd P hP hgP
  obtain ⟨b, hbP, hb⟩ := exists_real_mem_dd E g hpd P hP hgP
  have hc : algebraMap (𝓞 (maximalRealSubfield E)) E (b ^ ν.natAbs) ∈ dd E ^ ν.natAbs := by
    rw [map_pow]; exact pow_mem_pow E _ _ hb _
  have hcP : b ^ ν.natAbs ∉ P := fun h => hbP (hP.mem_of_pow_mem _ h)
  obtain ⟨h1, h2⟩ := span_zpow E _ ν hc
  set c := b ^ ν.natAbs
  ext t
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨c * a, fun hh => (hP.mem_or_mem hh).elim hcP ha, ?_⟩
    change _ ∈ idl E g k ν at h
    show _ ∈ idl E g k 0
    unfold idl at h ⊢
    rw [map_mul, mul_assoc, zpow_zero]
    have := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰
      (algebraMap (𝓞 (maximalRealSubfield E)) E c)) h
    rw [← mul_assoc] at this
    exact mul_le_mul' h1 le_rfl this
  · rintro ⟨a, ha, h⟩
    refine ⟨c * a, fun hh => (hP.mem_or_mem hh).elim hcP ha, ?_⟩
    change _ ∈ idl E g k 0 at h
    show _ ∈ idl E g k ν
    unfold idl at h ⊢
    rw [zpow_zero, one_mul] at h
    rw [map_mul, mul_assoc]
    exact mul_le_mul' h2 le_rfl (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰
      (algebraMap (𝓞 (maximalRealSubfield E)) E c)) h)
end Formalism.FourierDecayAlt.P.S6x2
