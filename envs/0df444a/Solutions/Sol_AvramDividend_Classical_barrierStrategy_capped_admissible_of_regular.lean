-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_capped_admissible_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T11:16:18.951054+00:00
-- url     : https://prove2.me/submissions/4fde0379-4c96-4451-bf5a-0ff9a91c741e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
import Theorems.Thm_AvramDividend_Classical_admissible_of_no_right_dividend_jumps

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) (hc : 0 ≤ c)
    (hleft : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X c c s ω) (Iic t) t)
    (hright : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X c c s ω) (Ici t) t)
    (hadapt : Adapted 𝓕 (barrierStrategy X c c)) :
    IsAdmissibleLe X c (ENNReal.ofReal c) (barrierStrategy X c c) := by
  have hm : ∀ ω, Monotone (fun t => barrierStrategy X c c t ω) :=
    barrierStrategy_monotone X c
  have hs : IsDividendStrategy 𝓕 (barrierStrategy X c c) := by
    refine ⟨?_, hm, hleft, hadapt⟩
    intro ω
    simp [barrierStrategy]
  have hrl : ∀ ω (t : ℝ≥0),
      rightLimit (barrierStrategy X c c) t ω =
        barrierStrategy X c c t ω := by
    intro ω t
    exact rightLimit_eq_of_monotone_right_continuous
      (barrierStrategy X c c) ω t (hm ω) (hright ω t)
  have ha : IsAdmissible X c (barrierStrategy X c c) :=
    admissible_of_no_right_dividend_jumps X c hc (barrierStrategy X c c) hs hrl
  exact ⟨ha, barrierStrategy_reserve_cap_bound X c⟩
