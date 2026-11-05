-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_postpayment_reserve_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:04:06.907861+00:00
-- url     : https://prove2.me/submissions/c7f1b7cd-1bea-450f-82d0-7527850ea76f

import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (Ici t) t := by
  have hX : ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω)
      (Ici t) t := X.rightCont ω t
  have hDlim : ContinuousWithinAt (fun s : ℝ≥0 => rightLimit D s ω)
      (Ici t) t :=
    dividendStrategy_rightLimit_rightContinuous D hD ω t
  exact (continuousWithinAt_const.add hX).sub hDlim
