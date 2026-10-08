-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_reserve_cap_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T21:17:37.253776+00:00
-- url     : https://prove2.me/submissions/2fdcda1d-1f15-4a79-8d8f-502ae65dd5cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_of_bddAbove

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0), 0 < t →
      ENNReal.ofReal (riskProcess X c (barrierStrategy X c c) t ω) ≤
        ENNReal.ofReal c := by
  intro ω t ht
  apply barrierStrategy_reserve_cap_bound_of_bddAbove X c ω t ht
  refine one_sided_limits_bddAbove_Icc (fun u => X.X u ω) ?_ ?_ t
  · intro u
    exact X.rightCont ω u
  · intro u
    by_cases hu : u = 0
    · subst u
      refine ⟨0, ?_⟩
      have hb : (𝓝[<] (0 : ℝ≥0)) = ⊥ :=
        nhdsLT_eq_bot_iff.mpr (.inl (fun v => (zero_le : (0 : ℝ≥0) ≤ v)))
      rw [hb]
      exact tendsto_bot
    · have hu_pos : 0 < u :=
        lt_of_le_of_ne ((zero_le : (0 : ℝ≥0) ≤ u)) (Ne.symm hu)
      exact X.leftLim ω u hu_pos
