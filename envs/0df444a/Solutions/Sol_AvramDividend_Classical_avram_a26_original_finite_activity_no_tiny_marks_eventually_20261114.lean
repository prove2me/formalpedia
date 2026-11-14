-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_finite_activity_no_tiny_marks_eventually_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:34:40.785406+00:00
-- url     : https://prove2.me/submissions/b6caf804-bc49-4e80-8a5c-f94199f737e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_finite_activity_physical_mark_gap_ae_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- For each compact source horizon, all sufficiently fine negative-jump omitted cutoff bands contain no physical marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n ≥ N, ∀ u : ℝ≥0,
      0 < u → u ≤ T →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        ∉ Ioo (-(1 / ((n : ℝ) + 1))) 0 := by
  filter_upwards [
    avram_a26_original_finite_activity_physical_mark_gap_ae_20261114
      X hFinite T] with ω hω
  obtain ⟨ε, hε, hGap⟩ := hω
  have hEventually : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventually
  refine ⟨N, ?_⟩
  intro n hn u hu0 huT
  intro hIn
  have hNonzero :
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    have ht := hIn.2
    exact ne_of_lt ht
  have hLower := hGap u hu0 huT hNonzero
  have hUpper := hN n hn
  have hInLower := hIn.1
  linarith
