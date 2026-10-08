-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T10:40:52.46365+00:00
-- url     : https://prove2.me/submissions/f3d74b8a-8509-4a51-b8bd-4e2e2ea9df84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted_of_countable_endpoint_representation

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    Adapted 𝓕 (barrierStrategy X c c) := by
  obtain ⟨S, hSCount, hSDense, hSBot, _⟩ :=
    exists_countable_dense_bot_top (ℝ≥0)
  have h0 : (0 : ℝ≥0) ∈ S := hSBot 0
    (fun v => (zero_le : (0 : ℝ≥0) ≤ v))
  have hbounded (t : ℝ≥0) (ω : Ω) :
      BddAbove (Set.range
        (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω)) := by
    refine one_sided_limits_bddAbove_Icc (fun u => X.X u ω) ?_ ?_ t
    · intro u
      exact X.rightCont ω u
    · intro u
      by_cases hu : u = 0
      · subst u
        refine ⟨0, ?_⟩
        have hb : (𝓝[<] (0 : ℝ≥0)) = ⊥ :=
          nhdsLT_eq_bot_iff.mpr (.inl
            (fun v => (zero_le : (0 : ℝ≥0) ≤ v)))
        rw [hb]
        exact tendsto_bot
      · have hupos : 0 < u :=
          lt_of_le_of_ne
            (zero_le : (0 : ℝ≥0) ≤ u) (Ne.symm hu)
        exact X.leftLim ω u hupos
  have hrep (t : ℝ≥0) (ω : Ω) :
      barrierStrategy X c c t ω =
        if t = 0 then 0 else
          max 0 (max
            (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω)
            (X.X t ω)) := by
    by_cases ht : t = 0
    · simp [barrierStrategy, ht]
    · have hsup :=
        dense_timeSup_with_endpoint (fun u => X.X u ω)
          (X.rightCont ω) S hSDense h0 t (hbounded t ω)
      simpa only [barrierStrategy, if_neg ht, sub_self, zero_add]
        using congrArg (max (0 : ℝ)) hsup
  exact barrierStrategy_adapted_of_countable_endpoint_representation
    X c S hSCount hrep
