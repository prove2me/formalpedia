-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_shifted_dense_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T01:14:10.378227+00:00
-- url     : https://prove2.me/submissions/4c03dd57-4de2-4f2b-8d77-5df1ca31319b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Every centred stopped Lévy future path has its real running maximum
    recovered exactly by its Borel countable clipped dense prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω)
      else 0).toReal =
    ⨆ s : Icc (0 : ℝ≥0) t,
      X.X (u + s.1) ω - X.X u ω := by
  simpa only [sSup_image'] using
    (avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
      X ω u samples hdense hzero t ht)
