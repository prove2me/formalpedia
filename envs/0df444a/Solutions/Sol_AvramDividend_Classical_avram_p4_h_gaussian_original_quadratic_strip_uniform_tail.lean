-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_quadratic_strip_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:19:20.440654+00:00
-- url     : https://prove2.me/submissions/1845ae9e-99d2-4a67-9776-d8439b4c4a9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
/-- Uniform quadratic compensator control for every original-process shrinking jump strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
      (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1)))
          (-(1 / ((m : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν) < ε := by
  have hTail :=
    avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero X
  have hEv : ∀ᶠ n : ℕ in atTop,
      (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
          ENNReal.ofReal (z ^ 2) ∂X.ν) < ε :=
    hTail.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEv
  refine ⟨N, ?_⟩
  intro n hn m
  have hsubset :
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))) ⊆
        Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hnonneg : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith [hz.2]
  exact lt_of_le_of_lt (lintegral_mono_set hsubset) (hN n hn)
