-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB79_original_postpayment_reserve_discontinuities_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:26:16.86982+00:00
-- url     : https://prove2.me/submissions/9d63bf06-dc0a-467a-ab71-2be01678c2fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB78_original_dividend_rightLimit_discontinuities_countable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (ω : Ω)
    (hX : Continuous (fun s : ℝ≥0 => X.X s ω)) :
    Set.Countable {t : ℝ≥0 |
      ¬ ContinuousAt (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} := by
  apply (avram_gbB78_original_dividend_rightLimit_discontinuities_countable D hD ω).mono
  intro t ht hDcont
  apply ht
  have hsum : ContinuousAt (fun s : ℝ≥0 => x + X.X s ω) t :=
    continuousAt_const.add hX.continuousAt
  exact hsum.sub hDcont
