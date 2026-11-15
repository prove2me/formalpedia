-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB259_original_future_increment_indepFun_prepayment_centre
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:54:50.642193+00:00
-- url     : https://prove2.me/submissions/10200563-3e4c-4cba-a850-9e8e0f4c658f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t) (x b : ℝ) :
    IndepFun
      (fun ω => b - x - X.X s ω + D s ω)
      (fun ω => X.X t ω - X.X s ω) P := by
  exact (IndepFun_iff_Indep _ _ P).2
    (avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
      X D hD s t hst x b).symm
