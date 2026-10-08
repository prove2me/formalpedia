-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_reserve_cap_bound_of_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T20:20:13.899073+00:00
-- url     : https://prove2.me/submissions/14215012-05cd-4885-ae26-28b8eebeea61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0), 0 < t →
      BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω)) →
      ENNReal.ofReal (riskProcess X c (barrierStrategy X c c) t ω) ≤
        ENNReal.ofReal c := by
  intro ω t ht hbdd
  have hsup :
      X.X t ω ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω := by
    exact le_ciSup hbdd
      ⟨t, ⟨(zero_le : (0 : ℝ≥0) ≤ t), le_rfl⟩⟩
  have hbar :
      barrierStrategy X c c t ω =
        max 0 (⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω) := by
    simp [barrierStrategy, ne_of_gt ht]
  apply ENNReal.ofReal_le_ofReal
  change c + X.X t ω - barrierStrategy X c c t ω ≤ c
  rw [hbar]
  have hm := le_trans hsup
    (le_max_right (0 : ℝ)
      (⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω))
  linarith
