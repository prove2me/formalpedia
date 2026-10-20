-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_ruinTime_le_barrier_ruinTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:33:35.713268+00:00
-- url     : https://prove2.me/submissions/01fe27fd-3366-475b-a399-02a299dd82bf

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_barrier_eq_control_before_ruin
import Theorems.Thm_AvramDividend_Classical_zero_cap_control_eq_levy_before_ruin
import Theorems.Thm_AvramDividend_Classical_ruinTime_le_of_nonnegative_before_first_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) :
    ruinTime X 0 D ω ≤ ruinTime X 0 (barrierStrategy X 0 0) ω := by
  apply ruinTime_le_of_nonnegative_before_first_ruin
    X 0 D (barrierStrategy X 0 0) ω
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simp [riskProcess, barrierStrategy, X.X_zero ω]
  · have hpos : 0 < t :=
        lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm ht0)
    have hB : barrierStrategy X 0 0 t ω = D t ω :=
      zero_cap_barrier_eq_control_before_ruin X D hD ω t hpos ht
    have hDval : D t ω = X.X t ω :=
      zero_cap_control_eq_levy_before_ruin X D hD ω t hpos ht
    simp [riskProcess, hB, hDval]
