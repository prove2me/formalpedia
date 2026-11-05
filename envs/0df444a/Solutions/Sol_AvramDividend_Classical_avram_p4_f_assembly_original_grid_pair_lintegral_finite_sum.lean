-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_grid_pair_lintegral_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:07:51.993894+00:00
-- url     : https://prove2.me/submissions/45dce628-6eca-4fac-bf46-dad1da74593b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin m, ∫⁻ ω, N 0 (s i) ω * N (s i) (t i) ω ∂P := by
  dsimp only
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
  change (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
    ∑ i : Fin m, ∫⁻ ω, N 0 (s i) ω * N (s i) (t i) ω ∂P
  apply lintegral_finset_sum
  intro i hi
  have hB : MeasurableSet B := measurableSet_Iic
  apply Measurable.mul
  · exact avram_p2_d_future_intrinsic_marked_rectangle_measurable X 0 (s i) B hB
  · exact avram_p2_d_future_intrinsic_marked_rectangle_measurable X (s i) (t i) B hB
