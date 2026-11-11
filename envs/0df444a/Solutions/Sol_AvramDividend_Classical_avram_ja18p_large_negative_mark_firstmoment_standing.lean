-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p_large_negative_mark_firstmoment_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:23:31.629506+00:00
-- url     : https://prove2.me/submissions/4049c713-14fa-4a61-a57d-8398a83bcef7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18p1_large_negative_firstmoment_of_laplace_slope
import Theorems.Thm_AvramDividend_Classical_avram_ja18p2_original_laplace_slope_bounded_below_of_standing
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) < ⊤ := by
  obtain ⟨C, hSlope⟩ :=
    avram_ja18p2_original_laplace_slope_bounded_below_of_standing X hX
  exact avram_ja18p1_large_negative_firstmoment_of_laplace_slope X C hSlope
