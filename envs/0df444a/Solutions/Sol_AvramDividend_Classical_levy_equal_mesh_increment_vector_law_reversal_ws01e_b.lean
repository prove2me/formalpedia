-- Prove2me | solution 1 for AvramDividend.Classical.levy_equal_mesh_increment_vector_law_reversal_ws01e_b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:28:06.903249+00:00
-- url     : https://prove2.me/submissions/d420d5ae-289e-42bd-bae3-fb18ad2ccf19

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_reversal_rectangles_ws01e_b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Equal-mesh Lévy increment vectors have the same law after coordinate reversal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hF : Measurable (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) :=
    measurable_pi_lambda _ fun i =>
      (X.adapted.measurable).sub (X.adapted.measurable)
  have hR : Measurable (fun ω : Ω => fun i : Fin n =>
      X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) :=
    measurable_pi_lambda _ fun i =>
      (X.adapted.measurable).sub (X.adapted.measurable)
  apply piPathMeasure_eq_of_finite_cylinder_masses
  · rw [Measure.map_apply hF MeasurableSet.univ]
    simp
  · intro J B hB
    let C : Fin n → Set ℝ := fun i => if i ∈ J then B i else univ
    have hC : ∀ i : Fin n, MeasurableSet (C i) := by
      intro i
      by_cases hi : i ∈ J
      · simpa [C, hi] using hB i hi
      · simp [C, hi]
    have hSet : Set.pi (J : Set (Fin n)) B =
        Set.pi Set.univ C := by
      ext f
      change (∀ i ∈ (J : Set (Fin n)), f i ∈ B i) ↔
        (∀ i ∈ (Set.univ : Set (Fin n)), f i ∈ C i)
      constructor
      · intro h i _
        by_cases hi : i ∈ J
        · simpa [C, hi] using (h i hi)
        · simp [C, hi]
      · intro h i hi
        have hci : f i ∈ C i := h i (Set.mem_univ i)
        have hfin : i ∈ J := hi
        dsimp [C] at hci
        simpa only [if_pos hfin] using hci
    have hM : MeasurableSet (Set.pi (Set.univ : Set (Fin n)) C) :=
      MeasurableSet.univ_pi hC
    rw [hSet, Measure.map_apply hF hM, Measure.map_apply hR hM]
    exact levy_equal_mesh_increment_reversal_rectangles_ws01e_b
      X δ n C hC
