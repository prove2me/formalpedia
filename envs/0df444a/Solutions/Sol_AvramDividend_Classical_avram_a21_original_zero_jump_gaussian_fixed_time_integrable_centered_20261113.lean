-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_zero_jump_gaussian_fixed_time_integrable_centered_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:17:42.691899+00:00
-- url     : https://prove2.me/submissions/1e5fb32a-4f59-42b9-878c-467671030fa8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The zero-jump Gaussian source, drift-centred at a fixed time, has mean zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) :
    Integrable (fun ω => Y.X t ω - (t : ℝ) * Y.c) P ∧
      (∫ ω, Y.X t ω - (t : ℝ) * Y.c ∂P) = 0 := by
  letI : IsProbabilityMeasure P := Y.isProbability
  have hInc :=
    avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
      Y hν 0 t (show (0 : ℝ≥0) ≤ t from zero_le)
  have hInt : Integrable (fun ω => Y.X t ω - (t : ℝ) * Y.c) P := by
    simpa [Y.X_zero] using hInc.1
  have hCond :
      P[(fun ω => Y.X t ω - (t : ℝ) * Y.c) | 𝓕.rightCont 0] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
    simpa [Y.X_zero] using hInc.2
  have hTotal :
      (∫ ω, P[(fun ω => Y.X t ω - (t : ℝ) * Y.c) | 𝓕.rightCont 0] ω ∂P) =
      (∫ ω, Y.X t ω - (t : ℝ) * Y.c ∂P) :=
    integral_condExp ((𝓕.rightCont).le 0)
  rw [integral_congr_ae hCond, integral_zero] at hTotal
  exact ⟨hInt, hTotal.symm⟩
