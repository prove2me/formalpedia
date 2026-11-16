-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a542_original_zerojump_gaussian_centred_increment_square_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:48:20.591211+00:00
-- url     : https://prove2.me/submissions/95b15c57-306b-4756-9d2c-c55b9142ec5a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a540_L2_envelope_dominates_any_fixed_increment_square
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) :
    Integrable (fun ω =>
      ((X.X t ω - (t : ℝ) * X.c) -
        (X.X s ω - (s : ℝ) * X.c))^2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun r ω =>
    X.X r ω - (r : ℝ) * X.c
  have hMart : Martingale M 𝓕.rightCont P :=
    avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
      X hNuZero
  have hMeas (r : ℝ≥0) (_ : r ≤ T) :
      AEStronglyMeasurable (M r) P :=
    ((hMart.stronglyAdapted r).mono (𝓕.rightCont.le r)).aestronglyMeasurable
  obtain ⟨S,hSint,hS⟩ :=
    avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
      X hNuZero T
  exact avram_ga_a540_L2_envelope_dominates_any_fixed_increment_square
    M T s t hs ht hMeas S hSint hS
