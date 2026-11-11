-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18q1_original_largejump_Campbell_exact_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:16:35.546758+00:00
-- url     : https://prove2.me/submissions/a09ca5a6-f287-44a1-9c0c-5831172e1a78

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18q1a_original_separated_borel_all_horizon_rate
import Theorems.Thm_AvramDividend_Classical_avram_ja18q1b_weighted_campbell_of_separated_rate
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
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ t : ℝ≥0,
      (∫⁻ ω, ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
        ENNReal.ofReal |p.2| ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
        (t : ℝ≥0∞) *
          (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) := by
  intro t
  apply avram_ja18q1b_weighted_campbell_of_separated_rate X t
  intro B hB hSep
  exact avram_ja18q1a_original_separated_borel_all_horizon_rate X t B hB hSep
