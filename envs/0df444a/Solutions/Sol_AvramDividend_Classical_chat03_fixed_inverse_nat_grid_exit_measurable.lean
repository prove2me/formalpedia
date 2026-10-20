-- Prove2me | solution 1 for AvramDividend.Classical.chat03_fixed_inverse_nat_grid_exit_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:50:20.336023+00:00
-- url     : https://prove2.me/submissions/86be4512-d200-429b-a844-380b0edc8185

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Measurability of every strict two-sided observation on a fixed
inverse-natural uniform grid follows directly from adaptedness.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (n k : ℕ) :
    MeasurableSet
      {ω : Ω |
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
  have hZ : Measurable
      (X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) :=
    (X.adapted _).mono (𝓕.le _) le_rfl
  exact (measurableSet_lt hZ measurable_const).union
    (measurableSet_lt measurable_const hZ)
