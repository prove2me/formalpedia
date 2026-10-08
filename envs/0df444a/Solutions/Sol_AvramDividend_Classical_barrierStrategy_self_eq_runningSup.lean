-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_self_eq_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T11:28:18.703984+00:00
-- url     : https://prove2.me/submissions/66fda6b7-9d12-4e82-af71-2116ff798d38

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) (ω : Ω) (t : ℝ≥0) :
    barrierStrategy X c c t ω = runningSup X t ω := by
  by_cases ht : t = 0
  · subst t
    rw [barrierStrategy, if_pos rfl]
    show (0 : ℝ) = ⨆ s : Icc (0 : ℝ≥0) 0, maxZero (X.X s.1 ω)
    letI : Subsingleton (Icc (0 : ℝ≥0) 0) :=
      ⟨fun a b =>
        Subtype.ext (Set.subsingleton_Icc_of_ge (le_refl 0) a.2 b.2)⟩
    rw [ciSup_subsingleton (i := (⟨0, by simp⟩ : Icc (0 : ℝ≥0) 0)) _]
    simp [maxZero, X.X_zero]
  · rw [barrierStrategy, if_neg ht, sub_self, zero_add]
    have h := runningSup_eq_rawSup_nonneg X t ω
    rw [← h.1]
    exact max_eq_right h.2
