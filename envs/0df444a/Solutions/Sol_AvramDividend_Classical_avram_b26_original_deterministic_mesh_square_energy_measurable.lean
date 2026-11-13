-- Prove2me | solution 1 for AvramDividend.Classical.avram_b26_original_deterministic_mesh_square_energy_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:47:03.093596+00:00
-- url     : https://prove2.me/submissions/56ba5e0e-ae23-4b00-b42a-f04ed2f208de

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original deterministic source mesh square energy has automatic measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0) :
    Measurable (fun ω : Ω => ∑ i ∈ S,
      (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c) ^ 2) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  have ht : Measurable (X.X (t i)) :=
    (X.adapted (t i)).mono (𝓕.le (t i)) le_rfl
  have hs : Measurable (X.X (s i)) :=
    (X.adapted (s i)).mono (𝓕.le (s i)) le_rfl
  exact ((ht.sub hs).sub measurable_const).pow_const 2
