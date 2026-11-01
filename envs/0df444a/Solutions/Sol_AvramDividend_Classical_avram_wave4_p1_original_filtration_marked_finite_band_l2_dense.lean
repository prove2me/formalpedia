-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_original_filtration_marked_finite_band_l2_dense
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:12:27.653109+00:00
-- url     : https://prove2.me/submissions/1a28319b-d2d5-4148-9c08-31bd8b8cb68f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_pi_system
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_generate_sigma
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pi_generator_l2_dense_after_lift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasurableSpace Set AvramDividend.Classical
open scoped ENNReal NNReal

/-- Finite-energy predictable marked kernels on the *original* filtration are
L² limits of finite real spans of original adapted-mark rectangle indicators.
This is a direct source-facing conclusion combining exact sigma generation,
the actual rectangle Pi-system, and proved measure-theoretic L² density.
It makes no assumption of source Poisson law or stochastic isometry. -/
theorem solution
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ)
    [mAll : MeasurableSpace ((ι × Ω) × E)]
    (μ : Measure ((ι × Ω) × E)) [IsFiniteMeasure μ]
    (hAll : mAll = (𝓕.predictable).prod mE) :
    let G : Set (Set (ι × Ω)) :=
      {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                S = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                S = (Set.Ioi i ×ˢ A))}
    let GM : Set (Set ((ι × Ω) × E)) :=
      Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
    let GP : Set (Set ((ι × Ω) × E)) :=
      insert Set.univ (insert (∅ : Set ((ι × Ω) × E)) GM)
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set ((ι × Ω) × E)) (ht : t ∈ GP)
        (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
        indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by
  classical
  let G : Set (Set (ι × Ω)) :=
    {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
              S = ({⊥} ×ˢ A)) ∨
         (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
              S = (Set.Ioi i ×ˢ A))}
  let GM : Set (Set ((ι × Ω) × E)) :=
    Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
  let GP : Set (Set ((ι × Ω) × E)) :=
    insert Set.univ (insert (∅ : Set ((ι × Ω) × E)) GM)
  let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
    {v | ∃ (t : Set ((ι × Ω) × E)) (ht : t ∈ GP)
      (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
      indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
  change ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
    f ∈ (Submodule.span ℝ S).topologicalClosure
  have hPi : IsPiSystem GM :=
    (avram_wave4_p1_predictable_marked_rectangle_pi_system 𝓕).2
  have hGen : mAll = MeasurableSpace.generateFrom GM :=
    hAll.trans (avram_wave4_p1_predictable_marked_rectangle_generate_sigma 𝓕)
  have hGm : ∀ t : Set ((ι × Ω) × E),
      t ∈ GM → MeasurableSet t := by
    intro t ht
    change MeasurableSet[mAll] t
    rw [hGen]
    exact MeasurableSpace.measurableSet_generateFrom ht
  exact avram_wave4_p1_pi_generator_l2_dense_after_lift μ GM hPi hGm hGen
