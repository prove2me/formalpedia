-- Prove2me | solution 1 for AvramDividend.Classical.cross_path_zero_count_law_of_finite_cylinders
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:52:36.930135+00:00
-- url     : https://prove2.me/submissions/e89bef24-a489-44da-b4d3-79c58953be66

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_finite_cylinder_masses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-!
Transfer the zero-event probability of a measurable path-counting functional
between distinct sample probability spaces with equal cylinder probabilities.
-/
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
      P₂ (Z ⁻¹' (Set.pi (J : Set ι) B)))
    (count : (ι → ℝ) → ℕ)
    (hCount : Measurable count) :
    P₁ {ω | count (Y ω) = 0} = P₂ {ω | count (Z ω) = 0} := by
  have hLaw : Measure.map Y P₁ = Measure.map Z P₂ :=
    cross_sample_path_law_eq_of_finite_cylinder_masses
      P₁ P₂ Y Z hY hZ hP hCyl
  have hZero : MeasurableSet {p : ι → ℝ | count p = 0} := by
    exact (measurableSet_singleton (0 : ℕ)).preimage hCount
  calc
    P₁ {ω | count (Y ω) = 0} =
        (Measure.map Y P₁) {p : ι → ℝ | count p = 0} := by
          rw [Measure.map_apply hY hZero]
          rfl
    _ = (Measure.map Z P₂) {p : ι → ℝ | count p = 0} :=
        congrArg (fun μ : Measure (ι → ℝ) =>
          μ {p : ι → ℝ | count p = 0}) hLaw
    _ = P₂ {ω | count (Z ω) = 0} := by
          rw [Measure.map_apply hZ hZero]
          rfl
