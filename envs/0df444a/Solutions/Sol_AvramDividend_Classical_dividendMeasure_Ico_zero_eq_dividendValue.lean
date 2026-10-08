-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_Ico_zero_eq_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:23:33.85007+00:00
-- url     : https://prove2.me/submissions/35d877a9-3e84-41df-a40f-822de0a3d4e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_monotone_leftcontinuous_stieltjes_measure_Ico
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_extension_leftContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    dividendMeasure D ω (Ico (0 : ℝ) (t : ℝ)) =
      ENNReal.ofReal (D t ω) := by
  have hmono : Monotone (fun s : ℝ => D s.toNNReal ω) := by
    intro a b hab
    exact (hD.2.1 ω) (Real.toNNReal_mono hab)
  have hleft := dividendStrategy_real_extension_leftContinuous D hD ω
  have hmass := monotone_leftcontinuous_stieltjes_measure_Ico
    (fun s : ℝ => D s.toNNReal ω) hmono hleft 0 (t : ℝ)
  have h0 : D 0 ω = 0 := hD.1 ω
  unfold dividendMeasure
  rw [dif_pos hmono]
  simpa [Real.toNNReal_coe, Real.toNNReal_zero, h0] using hmass
