-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_all_horizons_no_tiny_negative_marks_eventually_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:40:14.072595+00:00
-- url     : https://prove2.me/submissions/ed61650f-3cba-4e4a-9a85-330f6eb2b364

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_all_horizons_physical_negative_mark_margin_ae_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original finite-activity shrinking omitted negative mark bands are eventually empty on every horizon on one common source event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ N : ℕ, ∀ n ≥ N, ∀ u : ℝ≥0, 0 < u → u ≤ T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
          ∉ Ioo (-(1 / ((n : ℝ) + 1))) 0 := by
  filter_upwards [
    avram_a26_original_all_horizons_physical_negative_mark_margin_ae_20261114
      X hFinite] with ω hω
  intro T
  obtain ⟨ε, hε, hGap⟩ := hω T
  have hEventually : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventually
  refine ⟨N, ?_⟩
  intro n hn u hu0 huT
  intro hIn
  have hNonzero :
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 :=
    ne_of_lt hIn.2
  have hLower := hGap u hu0 huT hNonzero
  have hUpper := hN n hn
  have hInLower := hIn.1
  linarith
