-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_anyactivity_natural_negative_cutoff_compensated_cell_L1_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:48:13.759173+00:00
-- url     : https://prove2.me/submissions/5d39b539-bb98-4daf-8173-b682a09d2f49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    Integrable (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P ∧
      (∫ ω, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∂P) = 0 := by
  let δ : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by linarith)).2
    linarith
  let B : Set ℝ := Iic (-δ)
  have hB : MeasurableSet B := measurableSet_Iic
  have hNeg : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    change z ≤ -δ at hz
    have hneg : -δ < (0 : ℝ) := by linarith
    exact lt_of_le_of_lt hz hneg
  have hν : X.ν B < ⊤ :=
    avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
      X.ν X.ν_integrable δ hδ hδone
  exact avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
    X s t hst B hB hν hNeg
