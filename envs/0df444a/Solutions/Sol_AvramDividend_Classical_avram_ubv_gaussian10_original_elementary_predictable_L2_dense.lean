-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_elementary_predictable_L2_dense
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:20:57.257013+00:00
-- url     : https://prove2.me/submissions/a29b8a7c-d9c6-4174-b387-c7a23e3f0862

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_adapted_rectangle_sigma_generator
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_pi_system
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pi_generator_l2_dense_after_lift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasurableSpace Set TopologicalSpace AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι]
    [mProd : MeasurableSpace (ι × Ω)]
    (𝓕 : Filtration ι mΩ)
    (hProd : mProd = 𝓕.predictable)
    (μ : Measure (ι × Ω)) [IsFiniteMeasure μ] :
    let G : Set (Set (ι × Ω)) :=
      {T | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                 T = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                 T = (Set.Ioi i ×ˢ A))}
    let GP : Set (Set (ι × Ω)) := insert Set.univ (insert ∅ G)
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set (ι × Ω)) (ht : t ∈ GP)
        (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
        indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by
  classical
  let G : Set (Set (ι × Ω)) :=
    {T | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
               T = ({⊥} ×ˢ A)) ∨
         (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
               T = (Set.Ioi i ×ˢ A))}
  have hPi : IsPiSystem G :=
    (avram_wave4_p1_predictable_marked_rectangle_pi_system (E := Unit) 𝓕).1
  have hGen : mProd = MeasurableSpace.generateFrom G :=
    hProd.trans (avram_wave4_p1_predictable_adapted_rectangle_sigma_generator 𝓕)
  have hGm : ∀ t : Set (ι × Ω), t ∈ G → MeasurableSet t := by
    intro t ht
    rw [hGen]
    exact measurableSet_generateFrom ht
  exact avram_wave4_p1_pi_generator_l2_dense_after_lift μ G hPi hGm hGen
