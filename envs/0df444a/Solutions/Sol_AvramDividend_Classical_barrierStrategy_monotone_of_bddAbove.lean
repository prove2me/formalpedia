-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_monotone_of_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T22:59:07.854252+00:00
-- url     : https://prove2.me/submissions/087188ae-9776-40ac-b3d8-7d8b37fac8e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (hpath : ∀ ω (t : ℝ≥0),
      BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω))) :
    ∀ ω, Monotone (fun t => barrierStrategy X c c t ω) := by
  intro ω s t hst
  by_cases hs : s = 0
  · subst s
    have hzero : barrierStrategy X c c 0 ω = 0 := by
      simp [barrierStrategy]
    change barrierStrategy X c c 0 ω ≤ barrierStrategy X c c t ω
    rw [hzero]
    by_cases ht : t = 0
    · subst t
      simpa [barrierStrategy]
    · simp only [barrierStrategy, if_neg ht]
      exact le_max_left _ _
  · have hspos : 0 < s := lt_of_le_of_ne ((zero_le : (0 : ℝ≥0) ≤ s)) (Ne.symm hs)
    have htpos : 0 < t := hspos.trans_le hst
    have hsups :
        (⨆ v : Set.Icc (0 : ℝ≥0) s, X.X v.1 ω) ≤
          ⨆ v : Set.Icc (0 : ℝ≥0) t, X.X v.1 ω := by
      letI : Nonempty (Set.Icc (0 : ℝ≥0) s) :=
        ⟨⟨0, ⟨le_rfl, (zero_le : (0 : ℝ≥0) ≤ s)⟩⟩⟩
      refine ciSup_le fun v => ?_
      exact le_ciSup (hpath ω t)
        ⟨v.1, ⟨v.2.1, v.2.2.trans hst⟩⟩
    simp only [barrierStrategy, if_neg hs, if_neg (ne_of_gt htpos)]
    apply max_le_max_left
    apply add_le_add_right
    exact hsups
