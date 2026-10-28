-- Prove2me | solution 1 for AvramDividend.Classical.cross_sample_path_law_eq_of_finite_cylinder_masses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:30:37.178855+00:00
-- url     : https://prove2.me/submissions/5d3cf6c5-cb14-4a64-a914-545043258a8c

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω₁ Ω₂ ι : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (Y : Ω₁ → (ι → ℝ)) (Z : Ω₂ → (ι → ℝ))
    (hY : Measurable Y) (hZ : Measurable Z)
    (hP : P₁ univ ≠ ⊤)
    (hCyl : ∀ (J : Finset ι) (B : ι → Set ℝ),
      (∀ i ∈ J, MeasurableSet (B i)) →
      P₁ (Y ⁻¹' (Set.pi (J : Set ι) B)) =
      P₂ (Z ⁻¹' (Set.pi (J : Set ι) B))) :
    Measure.map Y P₁ = Measure.map Z P₂ := by
  apply piPathMeasure_eq_of_finite_cylinder_masses
  · rw [Measure.map_apply hY MeasurableSet.univ]
    exact hP
  · intro J B hB
    have hM : MeasurableSet (Set.pi (J : Set ι) B) :=
      MeasurableSet.pi J.countable_toSet hB
    rw [Measure.map_apply hY hM, Measure.map_apply hZ hM]
    exact hCyl J B hB
