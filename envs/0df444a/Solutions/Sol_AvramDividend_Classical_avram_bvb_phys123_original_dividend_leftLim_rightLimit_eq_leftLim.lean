-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:26:30.58079+00:00
-- url     : https://prove2.me/submissions/ab26cd95-37c6-4fe8-b3bb-1be4fadc08fb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- At a time with a nontrivial left neighbourhood, taking the
left limit of the original dividend rightLimit recovers its left limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hnb : (nhdsWithin t (Iio t)).NeBot) :
    Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) t =
      Function.leftLim (fun s : ℝ≥0 => D s ω) t := by
  letI : (nhdsWithin t (Iio t)).NeBot := hnb
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.1.1.2.1 ω
  have heq :
      (fun s : ℝ≥0 => rightLimit D s ω) =
        Function.rightLim (fun s : ℝ≥0 => D s ω) := by
    funext s
    exact avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
      X x C D hD ω s
  rw [heq]
  exact leftLim_rightLim (hmono.tendsto_leftLim t)
