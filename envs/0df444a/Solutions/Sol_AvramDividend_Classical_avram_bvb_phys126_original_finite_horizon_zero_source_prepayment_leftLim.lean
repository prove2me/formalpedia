-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:39:47.195228+00:00
-- url     : https://prove2.me/submissions/464e9329-04f4-49b5-8878-e8c7457cd849

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Original physical BV reserve left limit on a drift-only stopped
prefix, with source equality required only through the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S)
    (hnb : (nhdsWithin t (Iio t)).NeBot)
    (hsource : ∀ s : ℝ≥0, s ≤ S → X.X s ω = (s : ℝ) * X.drift) :
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t =
        x + (t : ℝ) * X.drift -
          Function.leftLim (fun s : ℝ≥0 => D s ω) t := by
  letI : (nhdsWithin t (Iio t)).NeBot := hnb
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.1.1.2.1 ω
  have hmonoR : Monotone (fun s : ℝ≥0 => rightLimit D s ω) := by
    have heq : (fun s : ℝ≥0 => rightLimit D s ω) =
        Function.rightLim (fun s : ℝ≥0 => D s ω) := by
      funext s
      exact avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
        X x C D hD ω s
    rw [heq]
    exact hmono.rightLim
  have hRlim := hmonoR.tendsto_leftLim t
  rw [avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
    X x C D hD ω t hnb] at hRlim
  have hlinear : ContinuousAt
      (fun s : ℝ≥0 => x + (s : ℝ) * X.drift) t := by
    fun_prop
  have hlt : Tendsto (fun s : ℝ≥0 => x + (s : ℝ) * X.drift)
      (nhdsWithin t (Iio t)) (𝓝 (x + (t : ℝ) * X.drift)) :=
    hlinear.tendsto.mono_left nhdsWithin_le_nhds
  have hdrift := hlt.sub hRlim
  have hevent :
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) =ᶠ[
        nhdsWithin t (Iio t)]
      (fun s : ℝ≥0 => x + (s : ℝ) * X.drift - rightLimit D s ω) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hsource s (le_trans (le_of_lt hs) ht)]
  exact leftLim_eq_of_tendsto (hdrift.congr' hevent.symm)
