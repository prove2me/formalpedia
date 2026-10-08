-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_Ico_eq_dividend_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:23:36.250094+00:00
-- url     : https://prove2.me/submissions/44b923aa-d208-407e-919a-14e25b07058f

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
    (ω : Ω) (a b : ℝ≥0) :
    dividendMeasure D ω (Ico (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (D b ω - D a ω) := by
  have hmono : Monotone (fun s : ℝ => D s.toNNReal ω) := by
    intro u v huv
    exact (hD.2.1 ω) (Real.toNNReal_mono huv)
  have hleft := dividendStrategy_real_extension_leftContinuous D hD ω
  have hmass := monotone_leftcontinuous_stieltjes_measure_Ico
    (fun s : ℝ => D s.toNNReal ω) hmono hleft (a : ℝ) (b : ℝ)
  unfold dividendMeasure
  rw [dif_pos hmono]
  simpa only [Real.toNNReal_coe] using hmass
