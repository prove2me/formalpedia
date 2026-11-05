-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_past_future_marked_pair_one_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:54:13.968121+00:00
-- url     : https://prove2.me/submissions/15a8d67b-a21e-4683-a14a-3d9ad6b9ffb1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_zero_origin_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc a b ×ˢ B)
    (∫⁻ ω, N 0 s ω * N s t ω ∂P) =
      ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  dsimp only
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
  change (∫⁻ ω, N 0 s ω * N s t ω ∂P) =
    ((s : ℝ≥0∞) * X.ν B) *
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
  have hB : MeasurableSet B := measurableSet_Iic
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hSep : B ⊆ Iic (-(1 / ((n : ℝ) + 1))) := by
    intro y hy
    exact hy
  have hPast : Measurable[𝓕 s] (N 0 s) :=
    avram_p4_f_assembly_original_past_count_raw_measurable_auto X s n
  have hMean : (∫⁻ ω, N 0 s ω ∂P) =
      (s : ℝ≥0∞) * X.ν B :=
    avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
      X s B hB (1 / ((n : ℝ) + 1)) hε hSep
  calc
    (∫⁻ ω, N 0 s ω * N s t ω ∂P) =
        (∫⁻ ω, N 0 s ω ∂P) *
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :=
      avram_p2_e_compensator_public_weighted_from_zero_origin_rate
        X s t hst B hB (N 0 s) hPast
    _ = ((s : ℝ≥0∞) * X.ν B) *
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
      rw [hMean]
