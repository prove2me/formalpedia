-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_adjacent_centred_increment_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:17:19.520856+00:00
-- url     : https://prove2.me/submissions/5057e43f-af32-4ca3-9c44-1099e0353749

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_adjacent_centred_increments_indep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- The actual Levy source's adjacent drift-centred increments are independent functions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun
      (fun ω => (Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c)
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
      P := by
  exact (IndepFun_iff_Indep _ _ P).2
    (avram_p4_a_gaussian_original_adjacent_centred_increments_indep
      Y s t u hst htu)
