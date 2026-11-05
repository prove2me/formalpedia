-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_preruin_discounted_positive_postpayment_terminal_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:57:18.709757+00:00
-- url     : https://prove2.me/submissions/0abeb637-5ef0-49c8-9e99-fe2160dc3cb4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous

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
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    ContinuousWithinAt
      (fun s : ℝ≥0 =>
        max 0 (Real.exp (-(q * (s : ℝ))) *
          w (x + X.X s ω - rightLimit D s ω)))
      {s : ℝ≥0 | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω} t := by
  let S : Set ℝ≥0 := {s | t ≤ s ∧ (s : ℝ≥0∞) < ruinTime X x D ω}
  have hw : ContinuousWithinAt
      (fun s : ℝ≥0 => w (x + X.X s ω - rightLimit D s ω)) S t :=
    avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
      X x D hD w hw_cont ω t ht
  have hexp : Continuous (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ)))) := by
    fun_prop
  have hprod : ContinuousWithinAt
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
        w (x + X.X s ω - rightLimit D s ω)) S t :=
    hexp.continuousWithinAt.mul hw
  exact continuousWithinAt_const.max hprod
