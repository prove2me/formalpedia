-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys124_original_zero_source_drift_prepayment_leftLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:32:05.860886+00:00
-- url     : https://prove2.me/submissions/a2a5ef8b-a196-4c9f-9b39-879e1540fda3

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

/-- Exact one-sided deterministic BV prepayment reserve identity
at an original positive-time left-limit point. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hnb : (nhdsWithin t (Iio t)).NeBot) :
    Function.leftLim (fun s : ℝ≥0 =>
      x + (s : ℝ) * X.drift - rightLimit D s ω) t =
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
  have hlt : Tendsto
      (fun s : ℝ≥0 => x + (s : ℝ) * X.drift)
      (nhdsWithin t (Iio t))
      (𝓝 (x + (t : ℝ) * X.drift)) :=
    hlinear.tendsto.mono_left nhdsWithin_le_nhds
  exact leftLim_eq_of_tendsto (hlt.sub hRlim)
