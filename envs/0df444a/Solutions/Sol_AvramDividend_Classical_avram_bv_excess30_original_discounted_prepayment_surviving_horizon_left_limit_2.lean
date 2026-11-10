-- Prove2me | solution 2 for AvramDividend.Classical.avram_bv_excess30_original_discounted_prepayment_surviving_horizon_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:02:44.38284+00:00
-- url     : https://prove2.me/submissions/2db6641c-5f88-4090-8dec-f9b8244d3056

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discounted original prepayment terminal is left-continuous on survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ((T : ℝ≥0∞) < ruinTime X x D ω) →
      Filter.Tendsto
        (fun s : ℝ≥0 =>
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω))
        (𝓝[<] T)
        (𝓝 (Real.exp (-(q * (T : ℝ))) *
          w (riskProcess X x D T ω))) := by
  have hbase :=
    avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae
      X D hD x w hw T hT
  filter_upwards [hbase] with ω hω
  intro hsurv
  have hdisc : Tendsto
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))))
      (𝓝[<] T) (𝓝 (Real.exp (-(q * (T : ℝ))))) := by
    have hc : Continuous (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ)))) :=
      Real.continuous_exp.comp
        ((continuous_const.mul NNReal.continuous_coe).neg)
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact hdisc.mul (hω hsurv)
