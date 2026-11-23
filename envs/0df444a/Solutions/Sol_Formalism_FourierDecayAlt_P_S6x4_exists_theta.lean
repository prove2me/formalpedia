-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x4.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:12.169405+00:00
-- url     : https://prove2.me/submissions/8de7eae9-705d-4309-826e-ed276a484473

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitPrimeToDifferent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x4_trace_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x4
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x4
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E]
    (h1 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤) :
    ∃ θ : 𝓞 E, (θ : E) + complexConj E (θ : E) = 1 := by
  set F := maximalRealSubfield E with hF
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FI E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [h1, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  let I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  have hI0 : (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    intro hb
    have : Algebra.intTrace (𝓞 F) (𝓞 E) 1 ∈ I := ⟨1, rfl⟩
    rw [hb, Ideal.mem_bot] at this
    have h2 := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) 1
    rw [this, map_zero, map_one, ← map_one (algebraMap F E), Algebra.trace_algebraMap,
      Algebra.IsQuadraticExtension.finrank_eq_two] at h2
    norm_num at h2
  have hinv : (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
    intro a ha
    rw [FractionalIdeal.mem_inv_iff hI0] at ha
    have hmem : algebraMap F E a ∈ FractionalIdeal.dual (𝓞 F) F (1 : FI E) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FI E) ≠ 0)]
      intro b hb
      rw [FractionalIdeal.mem_one_iff] at hb
      obtain ⟨z, rfl⟩ := hb
      rw [Algebra.traceForm_apply, ← Algebra.smul_def, map_smul, smul_eq_mul,
        ← Algebra.algebraMap_intTrace (A := 𝓞 F)]
      have := ha (algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) z))
        ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, ⟨z, rfl⟩, rfl⟩)
      rw [FractionalIdeal.mem_one_iff] at this
      exact this
    rw [hdual, FractionalIdeal.mem_one_iff] at hmem
    obtain ⟨z, hz⟩ := hmem
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective F E), ← hz]
      exact z.isIntegral_coe
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨⟨a, hint⟩, rfl⟩
  have hone : (1 : FractionalIdeal (𝓞 F)⁰ F) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 F)⁰ F) = I * (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
          (mul_inv_cancel₀ hI0).symm
      _ ≤ I * 1 := mul_le_mul_right hinv _
      _ = I := mul_one _
  have h1I : (1 : F) ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := hone (FractionalIdeal.one_mem_one _)
  rw [FractionalIdeal.mem_coeIdeal] at h1I
  obtain ⟨w, ⟨θ, hθ⟩, hw⟩ := h1I
  refine ⟨θ, ?_⟩
  rw [← trace_rel, ← hF]
  have h2 := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) θ
  rw [hθ, hw] at h2
  rw [show ((θ : E)) = algebraMap (𝓞 E) E θ from rfl, ← h2, map_one]
end Formalism.FourierDecayAlt.P.S6x4
