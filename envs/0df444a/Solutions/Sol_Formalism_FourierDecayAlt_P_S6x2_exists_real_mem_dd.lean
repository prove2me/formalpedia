-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.exists_real_mem_dd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:13.595668+00:00
-- url     : https://prove2.me/submissions/1ae94caa-7665-417c-bd2c-1f131a6356b3

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff

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
theorem _root_.solution (g : ℕ) (hpd : PrimeToDifferent E g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsPrime)
    (hgP : (g : 𝓞 (maximalRealSubfield E)) ∈ P) :
    ∃ b : 𝓞 (maximalRealSubfield E), b ∉ P ∧
      algebraMap (𝓞 (maximalRealSubfield E)) E b ∈ dd E := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1
    ((Ideal.isCoprime_iff_sup_eq.1 hpd) ▸ (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hfix : complexConj E ((x * ringOfIntegersComplexConj E x : 𝓞 E) : E)
      = ((x * ringOfIntegersComplexConj E x : 𝓞 E) : E) := by
    simp [mul_comm]
  obtain ⟨b, hb⟩ := (RingOfIntegers.complexConj_eq_self_iff E _).1 hfix
  refine ⟨b, ?_, ?_⟩
  · intro hbP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 E)) (by simp)
    have hb' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) b
        = x * ringOfIntegersComplexConj E x := RingOfIntegers.ext hb
    have h1 : x * ringOfIntegersComplexConj E x ∈ Q := by
      rw [← hb', ← Ideal.mem_comap, hQP.2]; exact hbP
    have h2 : (g : 𝓞 E) ∈ Q := by
      have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (g : 𝓞 (maximalRealSubfield E)) ∈ Q := by
        rw [← Ideal.mem_comap, hQP.2]; exact hgP
      simpa using this
    have hx1 : x = 1 - w * g := by rw [← hxy]; ring
    apply hQP.1.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 E) = x * ringOfIntegersComplexConj E x
        + (g : 𝓞 E) * (w + ringOfIntegersComplexConj E w - w * ringOfIntegersComplexConj E w * g) := by
      rw [hx1, map_sub, map_mul, map_one, map_natCast]; ring
    rw [e]
    exact Q.add_mem h1 (Q.mul_mem_right _ h2)
  · rw [hb]
    unfold dd
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, Ideal.mul_mem_right _ _ hx, rfl⟩
end Formalism.FourierDecayAlt.P.S6x2
