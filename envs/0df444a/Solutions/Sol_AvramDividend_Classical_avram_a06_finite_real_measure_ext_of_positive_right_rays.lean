-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_finite_real_measure_ext_of_positive_right_rays
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:23:29.285053+00:00
-- url     : https://prove2.me/submissions/9f8d749a-f87b-4e4f-ae7b-4ba4a66a5ff5

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Positive-support finite real measures are identified by their tail mass
    on all nonnegative right rays. -/
theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (hMass : μ Set.univ = ν Set.univ)
    (hSupport : μ (Set.Ioi 0) = μ Set.univ)
    (hRay : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioi t) = ν (Set.Ioi t)) :
    μ = ν := by
  have hνSupport : ν (Ioi (0 : ℝ)) = ν univ := by
    calc
      ν (Ioi (0 : ℝ)) = μ (Ioi 0) := (hRay 0 le_rfl).symm
      _ = μ univ := hSupport
      _ = ν univ := hMass
  have hAll (t : ℝ) : μ (Ioi t) = ν (Ioi t) := by
    by_cases ht : 0 ≤ t
    · exact hRay t ht
    · have hlt : t < 0 := lt_of_not_ge ht
      have hsub : Ioi (0 : ℝ) ⊆ Ioi t := by
        intro x hx
        exact lt_trans hlt hx
      have hμ : μ (Ioi t) = μ univ := by
        apply le_antisymm (measure_mono (subset_univ _))
        calc
          μ univ = μ (Ioi 0) := hSupport.symm
          _ ≤ μ (Ioi t) := measure_mono hsub
      have hν : ν (Ioi t) = ν univ := by
        apply le_antisymm (measure_mono (subset_univ _))
        calc
          ν univ = ν (Ioi 0) := hνSupport.symm
          _ ≤ ν (Ioi t) := measure_mono hsub
      exact hμ.trans (hMass.trans hν.symm)
  haveI : IsFiniteMeasure ν := ⟨by simp [← hMass]⟩
  apply Measure.ext_of_Iic μ ν
  intro a
  calc
    μ (Iic a) = μ univ - μ (Ioi a) := by
      simpa only [Set.compl_Ioi] using
        (measure_compl (measurableSet_Ioi) (measure_ne_top μ (Ioi a)))
    _ = ν univ - ν (Ioi a) := by rw [hMass, hAll]
    _ = ν (Iic a) := by
      simpa only [Set.compl_Ioi] using
        (measure_compl (measurableSet_Ioi) (measure_ne_top ν (Ioi a))).symm
