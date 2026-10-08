-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T09:40:36.1303+00:00
-- url     : https://prove2.me/submissions/6053a750-5ef8-4f81-aaab-fac2eb8fedee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone_of_bddAbove

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω, Monotone (fun t => barrierStrategy X c c t ω) := by
  apply barrierStrategy_monotone_of_bddAbove X c
  intro ω t
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
