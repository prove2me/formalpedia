-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f14_original_near_zero_rational_path_equiv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:20:53.085404+00:00
-- url     : https://prove2.me/submissions/4fc27b2d-aac2-4841-b52f-404a152f7b20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_AvramDividend_Classical_avram_p4_f15_continuousWithin_positive_rational_witness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original Lévy near-zero positivity is witnessed on the nonnegative rational clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} =
      {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < X.X (q : ℝ≥0) ω} := by
  ext ω
  constructor
  · intro h ε hε
    obtain ⟨s, hsε, hsPos⟩ := h ε hε
    obtain ⟨q, _hsq, hqε, hqPos⟩ :=
      avram_p4_f15_continuousWithin_positive_rational_witness
        (fun t => X.X t ω) s ε hsε hsPos (X.rightCont ω s)
    exact ⟨q, hqε, hqPos⟩
  · intro h ε hε
    obtain ⟨q, hqε, hqPos⟩ := h ε hε
    exact ⟨q, hqε, hqPos⟩
