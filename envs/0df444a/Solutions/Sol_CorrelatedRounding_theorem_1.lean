-- Prove2me | solution 1 for CorrelatedRounding.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-17T05:43:09.475201+00:00
-- url     : https://prove2.me/submissions/0fbedc4c-faed-4596-a7ec-53c0df89e307
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw
import Definitions.Def_CorrelatedRounding_alg1Prog
import Theorems.Thm_CorrelatedRounding_runtime_claim
import Theorems.Thm_CorrelatedRounding_lemma_1
import Theorems.Thm_CorrelatedRounding_exists_alg1_draw__p2m_61ba9ba4_6281_4f25_8ae8_6ab3c87d78d1_a1
import Theorems.Thm_CorrelatedRounding_competitive_bound__p2m_61ba9ba4_6281_4f25_8ae8_6ab3c87d78d1_a1

open CorrelatedRounding MeasureTheory ProbabilityTheory

theorem solution :
    ∃ C : ℕ, ∀ (q K : ℕ), 1 ≤ q → ∀ (u : Fin K → Fin q → ℝ), IsInstance u →
      (∀ E : Fin K → ℝ,
        ((alg1Prog u E).run 0).2 ≤ C * q * K ∧
        ∃ z : Fin q → Fin K, (∀ i, ((alg1Prog u E).run 0).1 i = some (z i)) ∧ IsAlg1Output u E z) ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (E : Fin K → Ω → ℝ), IsAlg1Draw u μ E) ∧
      (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Fin K → Ω → ℝ), IsAlg1Draw u μ E →
        ∀ Z : Ω → Fin q → Fin K, (∀ᵐ ω ∂μ, IsAlg1Output u (fun k => E k ω) (Z ω)) →
          (∀ i k, μ {ω | Z ω i = k} = ENNReal.ofReal (u k i)) ∧
          ∀ k, μ (⋃ i, {ω | Z ω i = k}) ≤ ENNReal.ofReal ((1 + Real.log q) * y u k)) := by
  obtain ⟨C, hC⟩ := CorrelatedRounding.runtime_claim
  refine ⟨C, ?_⟩
  intro q K hq u hu
  refine ⟨?_, ?_, ?_⟩
  · exact hC q K hq u hu
  · exact CorrelatedRounding.exists_alg1_draw__p2m_61ba9ba4_6281_4f25_8ae8_6ab3c87d78d1_a1 q K hq u hu
  · intro Ω _ μ _ E hE Z hZ
    constructor
    · intro i k
      exact CorrelatedRounding.lemma_1 hu hE hZ i k
    · exact CorrelatedRounding.competitive_bound__p2m_61ba9ba4_6281_4f25_8ae8_6ab3c87d78d1_a1 hq μ u hu E hE Z hZ
