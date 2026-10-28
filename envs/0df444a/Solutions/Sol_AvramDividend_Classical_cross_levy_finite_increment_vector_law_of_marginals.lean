-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_finite_increment_vector_law_of_marginals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:37:28.049765+00:00
-- url     : https://prove2.me/submissions/41ff6666-edbf-46ad-85fe-6ec53436266a

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
import Theorems.Thm_AvramDividend_Classical_cross_levy_prefix_increment_rectangles_of_marginal_laws

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hMarginal : ∀ u : ℝ≥0, Measure.map (X.X u) P₁ = Measure.map (Y.X u) P₂)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    Measure.map (fun ω : Ω₁ => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun i : Fin n =>
      Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) P₂ := by
  letI : IsProbabilityMeasure P₁ := X.isProbability
  have hX : Measurable (fun ω : Ω₁ => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) :=
    measurable_pi_lambda _ fun i =>
      (X.adapted.measurable).sub (X.adapted.measurable)
  have hY : Measurable (fun ω : Ω₂ => fun i : Fin n =>
      Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) :=
    measurable_pi_lambda _ fun i =>
      (Y.adapted.measurable).sub (Y.adapted.measurable)
  apply piPathMeasure_eq_of_finite_cylinder_masses
  · rw [Measure.map_apply hX MeasurableSet.univ]
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
    rw [hSet, Measure.map_apply hX hM, Measure.map_apply hY hM]
    exact cross_levy_prefix_increment_rectangles_of_marginal_laws
      X Y hMarginal t ht n C hC
