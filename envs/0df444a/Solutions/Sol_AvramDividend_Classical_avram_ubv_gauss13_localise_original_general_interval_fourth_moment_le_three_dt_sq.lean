-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:30:56.995376+00:00
-- url     : https://prove2.me/submissions/dc6a7dda-48aa-48c2-b0b9-cfe571eb826c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_identdistrib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_fourth_moment_le_three_time_sq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hMeas : Measurable (fun ω : Ω =>
      (X.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ)) :
    (∫⁻ ω, ENNReal.ofReal
      ((((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) ^ 4) ∂P) ≤
    ENNReal.ofReal (3 * (((t - s : ℝ≥0) : ℝ) ^ 2)) := by
  have hID :=
    avram_p4_a_gaussian_original_centred_increment_identdistrib X s t hst
  have hComp := hID.comp
    (show Measurable (fun y : ℝ => ENNReal.ofReal ((y / X.σ) ^ 4)) by fun_prop)
  have hEq :
      (∫⁻ ω, ENNReal.ofReal
        ((((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) ^ 4) ∂P) =
      (∫⁻ ω, ENNReal.ofReal
        (((X.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) ^ 4) ∂P) := by
    exact hComp.lintegral_eq
  calc
    (∫⁻ ω, ENNReal.ofReal
      ((((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) ^ 4) ∂P) =
      (∫⁻ ω, ENNReal.ofReal
        (((X.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) ^ 4) ∂P) := hEq
    _ ≤ ENNReal.ofReal (3 * (((t - s : ℝ≥0) : ℝ) ^ 2)) :=
      avram_ubv_gauss13_localise_original_fourth_moment_le_three_time_sq
        X hν hσ (t - s) hMeas
