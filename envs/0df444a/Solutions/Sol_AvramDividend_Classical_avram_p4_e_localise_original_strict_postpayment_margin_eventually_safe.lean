-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_strict_postpayment_margin_eventually_safe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:05:22.793911+00:00
-- url     : https://prove2.me/submissions/2c6169c5-a831-4526-b27f-23c40f8e263c

import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (hMargin : 0 < x + X.X 0 ω - rightLimit D 0 ω) :
    ∀ᶠ s in 𝓝[≥] (0 : ℝ≥0),
      0 < x + X.X s ω - rightLimit D s ω := by
  have hX : ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω)
      (Ici (0 : ℝ≥0)) 0 := X.rightCont ω 0
  have hDlim : ContinuousWithinAt (fun s : ℝ≥0 => rightLimit D s ω)
      (Ici (0 : ℝ≥0)) 0 :=
    dividendStrategy_rightLimit_rightContinuous D hD ω 0
  have hc : ContinuousWithinAt
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (Ici (0 : ℝ≥0)) 0 :=
    (continuousWithinAt_const.add hX).sub hDlim
  exact hc.tendsto.eventually (Ioi_mem_nhds hMargin)
