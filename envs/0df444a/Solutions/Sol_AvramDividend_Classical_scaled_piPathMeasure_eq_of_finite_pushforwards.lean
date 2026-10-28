-- Prove2me | solution 1 for AvramDividend.Classical.scaled_piPathMeasure_eq_of_finite_pushforwards
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:41:58.117284+00:00
-- url     : https://prove2.me/submissions/bc7a2b08-7711-455d-bc78-fb9aae4e57c3

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_map_eq_of_finite_pushforwards

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Scalar finite-dimensional distribution identities determine a full scaled path law. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {μ ν : Measure Ω}
    (Y Z : Ω → (ι → ℝ))
    (hY : Measurable Y) (hZ : Measurable Z)
    (c : ℝ≥0∞)
    (hMass : (Measure.map Y μ) Set.univ ≠ ⊤)
    (hFinite : ∀ J : Finset ι,
      Measure.map (fun ω : Ω => fun j : J => Y ω j) μ =
        c • Measure.map (fun ω : Ω => fun j : J => Z ω j) ν) :
    Measure.map Y μ = c • Measure.map Z ν := by
  classical
  have hFinite' : ∀ J : Finset ι,
      Measure.map (fun ω : Ω => fun j : J => Y ω j) μ =
        Measure.map (fun ω : Ω => fun j : J => Z ω j) (c • ν) := by
    intro J
    have hZJ : Measurable (fun ω : Ω => fun j : J => Z ω j) := by
      apply measurable_pi_iff.mpr
      intro j
      exact (measurable_pi_apply (j : ι)).comp hZ
    rw [Measure.map_smul]
    exact hFinite J
  have hLaw :=
    piPathMeasure_map_eq_of_finite_pushforwards
      Y Z hY hZ hMass hFinite'
  rw [Measure.map_smul] at hLaw
  exact hLaw
