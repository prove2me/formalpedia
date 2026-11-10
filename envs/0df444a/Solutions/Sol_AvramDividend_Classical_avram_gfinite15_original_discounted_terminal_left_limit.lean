-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite15_original_discounted_terminal_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T16:34:00.15979+00:00
-- url     : https://prove2.me/submissions/6de48f3d-51e5-4609-8bd9-35ca8e804993

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_positive_clock_w_left_payoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! At genuine positive physical times, continuous exponential discount
preserves the original postpayment value's almost-sure left limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) ≤ ruinTime X x D ω →
      Tendsto
        (fun s : ℝ≥0 =>
          Real.exp (-(q * (s : ℝ))) *
            w (x + X.X s ω - rightLimit D s ω))
        (𝓝[<] t)
        (𝓝 (Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω))) := by
  filter_upwards [avram_ubv_finite12_original_positive_clock_w_left_payoff
    X hν x C D hD w hw] with ω hω
  intro t ht hstop
  have hc : Continuous (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ)))) := by
    fun_prop
  have he : Tendsto (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))))
      (𝓝[<] t) (𝓝 (Real.exp (-(q * (t : ℝ))))) := by
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact he.mul (hω t ht hstop)
