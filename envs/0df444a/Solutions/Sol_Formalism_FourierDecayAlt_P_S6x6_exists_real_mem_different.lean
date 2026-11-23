-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.exists_real_mem_different
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:39.642801+00:00
-- url     : https://prove2.me/submissions/5587f5b8-3120-4263-9a60-ff712fe6fb30

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_conj_conj

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
namespace Formalism.FourierDecayAlt.P.S6x6
theorem _root_.solution (g : ℕ) (hc : PrimeToDifferent E g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsPrime)
    (hgP : (g : 𝓞 (maximalRealSubfield E)) ∈ P) :
    ∃ a : 𝓞 (maximalRealSubfield E), a ∉ P ∧
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a ∈ differentIdeal ℤ (𝓞 E) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp hc
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hfix : ringOfIntegersComplexConj E (x * ringOfIntegersComplexConj E x) =
      x * ringOfIntegersComplexConj E x := by
    rw [map_mul, conj_conj, mul_comm]
  obtain ⟨a, ha⟩ := (ringOfIntegersComplexConj_eq_self_iff E _).mp hfix
  have hfix2 : ringOfIntegersComplexConj E (w + ringOfIntegersComplexConj E w -
      (g : 𝓞 E) * (w * ringOfIntegersComplexConj E w)) =
      w + ringOfIntegersComplexConj E w - (g : 𝓞 E) * (w * ringOfIntegersComplexConj E w) := by
    simp only [map_sub, map_add, map_mul, conj_conj, map_natCast]
    ring
  obtain ⟨b, hb⟩ := (ringOfIntegersComplexConj_eq_self_iff E _).mp hfix2
  have hx' : x = 1 - w * (g : 𝓞 E) := by rw [← hxy]; ring
  have hab : a + (g : 𝓞 (maximalRealSubfield E)) * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E)
    rw [map_add, map_mul, ha, hb, map_natCast, map_one, hx']
    simp only [map_sub, map_mul, map_one, map_natCast]
    ring
  refine ⟨a, fun haP => hP.ne_top ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one, ← hab]
    exact P.add_mem haP (P.mul_mem_right _ hgP)
  · rw [ha]; exact Ideal.mul_mem_right _ _ hx
end Formalism.FourierDecayAlt.P.S6x6
