-- Prove2me | solution 1 for FoundationsML.RademacherVC.rademacher_generalization_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:14:09.741405+00:00
-- url     : https://prove2.me/submissions/2904e442-9b26-4fb3-865a-f8be8cba35a3

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_RademacherComplexity

open MeasureTheory

namespace FoundationsML.RademacherVC

universe u

theorem rad_counter :
    ¬ (∀ {Z : Type u} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (G : Set (Z → ℝ)) (hGb : ∀ g ∈ G, ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hGm : ∀ g ∈ G, Measurable g)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → Z | ∀ g ∈ G, (∫ z, g z ∂D) ≤
        (1 / (m : ℝ)) * ∑ i, g (S i) + 2 * RademacherComplexity D G m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro H
  have h := H (Z := PUnit.{u+1}) (Measure.dirac PUnit.unit) {fun _ => (1:ℝ)}
    (by intro g hg z; simp at hg; subst hg; simp) (by intro g hg; simp at hg; subst hg; exact measurable_const)
    0 (1/2) (by norm_num)
  have hR : RademacherComplexity (Measure.dirac PUnit.unit.{u+1}) {fun _ : PUnit.{u+1} => (1:ℝ)} 0 = 0 := by
    unfold RademacherComplexity EmpiricalRademacherComplexity
    simp
  simp [hR] at h
  norm_num at h

end FoundationsML.RademacherVC

open FoundationsML.RademacherVC

theorem solution :
    ¬ (∀ {Z : Type} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (G : Set (Z → ℝ)) (hGb : ∀ g ∈ G, ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hGm : ∀ g ∈ G, Measurable g)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → Z | ∀ g ∈ G, (∫ z, g z ∂D) ≤
        (1 / (m : ℝ)) * ∑ i, g (S i) + 2 * RademacherComplexity D G m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  exact rad_counter.{0}
