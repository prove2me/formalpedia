-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_indicator_l2_adapted_algebra_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T18:08:26.253582+00:00
-- url     : https://prove2.me/submissions/58221301-77a4-4d92-9106-c43ea2d5f32b

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_generator_set_algebra_measure_dense

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set TopologicalSpace AvramDividend.Classical
open scoped ENNReal NNReal

/-- Every original-filtration predictable finite-measure indicator has an L²
approximation by indicators of finite Boolean combinations of adapted
past-measurable time rectangles, on the same time-history measure μ. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    [mProd : MeasurableSpace (ι × Ω)]
    (hProd : mProd = 𝓕.predictable)
    (μ : Measure (ι × Ω)) [IsFiniteMeasure μ]
    (s : Set (ι × Ω)) (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (c : ℝ) :
    let G : Set (Set (ι × Ω)) :=
      {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                S = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                S = (Set.Ioi i ×ˢ A))}
    ∃ (hG : μ.MeasureDense (generateSetAlgebra G)),
      indicatorConstLp (2 : ℝ≥0∞) hs hμs c ∈
        closure {indicatorConstLp (2 : ℝ≥0∞) (hG.measurable t ht) hμt c |
          (t : Set (ι × Ω)) (ht : t ∈ generateSetAlgebra G) (hμt : μ t ≠ ⊤)} := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let G : Set (Set (ι × Ω)) :=
    {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
              S = ({⊥} ×ˢ A)) ∨
         (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
              S = (Set.Ioi i ×ˢ A))}
  change ∃ (hG : μ.MeasureDense (generateSetAlgebra G)),
      indicatorConstLp (2 : ℝ≥0∞) hs hμs c ∈
        closure {indicatorConstLp (2 : ℝ≥0∞) (hG.measurable t ht) hμt c |
          (t : Set (ι × Ω)) (ht : t ∈ generateSetAlgebra G) (hμt : μ t ≠ ⊤)}
  have hG : μ.MeasureDense (generateSetAlgebra G) :=
    avram_wave4_p1_predictable_generator_set_algebra_measure_dense 𝓕 hProd μ
  refine ⟨hG, ?_⟩
  exact hG.indicatorConstLp_subset_closure (2 : ℝ≥0∞) c
    ⟨s, hs, hμs, rfl⟩