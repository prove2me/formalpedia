-- Prove2me | solution 2 for AvramDividend.Classical.piPathMeasure_eq_of_finite_cylinder_masses
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:25:48.081393+00:00
-- url     : https://prove2.me/submissions/fe8a88d8-213f-493d-a4d3-968b6c8b82b4

import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product

open MeasureTheory Set
open scoped ENNReal
theorem solution
    {ι : Type*} (μ ν : Measure (ι → ℝ))
    (hFinite : μ Set.univ ≠ ⊤)
    (hCyl : ∀ (J : Finset ι) (B : ι → Set ℝ),
      (∀ i ∈ J, MeasurableSet (B i)) →
      μ (Set.pi (J : Set ι) B) = ν (Set.pi (J : Set ι) B)) :
    μ = ν := by
  have huniv : μ Set.univ = ν Set.univ := by
    simpa using hCyl ∅ (fun _ => Set.univ) (by simp)
  haveI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.2 hFinite⟩
  refine ext_of_generate_finite _ generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun i => MeasurableSpace.isPiSystem_measurableSet)
      (fun i => (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ)))) ?_ huniv
  rintro S ⟨J, B, hB, rfl⟩
  exact hCyl J B fun i _ => hB i (Set.mem_univ i)
