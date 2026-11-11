-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18q1a_original_separated_borel_all_horizon_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:17:57.795789+00:00
-- url     : https://prove2.me/submissions/159358bb-f0a5-4939-8853-16b75a9fac0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2
import Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_separated_negative_borel_levy_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hSep : B ⊆ Iic (-1 : ℝ)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B) ∂P) =
      (t : ℝ≥0∞) * X.ν B := by
  obtain ⟨σ, hσ, _, _, _, _⟩ :=
    avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2 X
  have hOne := hσ 1 B hB
  have hUnit :=
    avram_integration_original_unit_separated_negative_borel_levy_rate
      X B hB 1 (by norm_num) hSep
  have hSigma : σ B = X.ν B := by
    calc
      σ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
        simpa using hOne.symm
      _ = X.ν B := hUnit
  rw [hσ t B hB, hSigma]
