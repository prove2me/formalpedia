-- Prove2me | solution 1 for AvramDividend.Classical.avram_b107_original_source_negative_jump_iff_some_cutoff_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:16:47.930079+00:00
-- url     : https://prove2.me/submissions/bbd1348e-a497-4caf-a0a7-6167e0844cd2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    (∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0) ↔
    (∃ n : ℕ, ∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))) := by
  constructor
  · rintro ⟨u, hsu, hut, hNeg⟩
    have hPos : 0 < -(X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by linarith
    obtain ⟨n, hSmall⟩ := exists_nat_one_div_lt hPos
    refine ⟨n, u, hsu, hut, ?_⟩
    linarith
  · rintro ⟨n, u, hsu, hut, hBound⟩
    refine ⟨u, hsu, hut, ?_⟩
    have hPos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
