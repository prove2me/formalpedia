-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_right_increment_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:37:24.170221+00:00
-- url     : https://prove2.me/submissions/68ed587a-3069-4c44-a9e7-94039d875538

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) :
    ∀ ω (t : ℝ≥0),
      rightLimit (barrierStrategy X x a) t ω - barrierStrategy X x a t ω =
        if t = 0 then max 0 (x - a) else 0 := by
  intro ω t
  let E : ℝ≥0 → Ω → ℝ := fun u ξ =>
    max 0 (x - a + runningSup X u ξ)
  have hpath (u : ℝ≥0) :
      BddAbove (Set.range
        (fun s : Set.Icc (0 : ℝ≥0) u => X.X s.1 ω)) := by
    refine one_sided_limits_bddAbove_Icc (fun v => X.X v ω) ?_ ?_ u
    · intro v
      exact X.rightCont ω v
    · intro v
      by_cases hv : v = 0
      · subst v
        refine ⟨0, ?_⟩
        have hb : (𝓝[<] (0 : ℝ≥0)) = ⊥ :=
          nhdsLT_eq_bot_iff.mpr
            (.inl (fun z => (zero_le : (0 : ℝ≥0) ≤ z)))
        rw [hb]
        exact tendsto_bot
      · have hvpos : 0 < v :=
          lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ v) (Ne.symm hv)
        exact X.leftLim ω v hvpos
  have hmonoM : Monotone (fun u => runningSup X u ω) := by
    intro s u hsu
    change runningSup X s ω ≤ runningSup X u ω
    rw [(runningSup_eq_rawSup_nonneg X s ω).1,
      (runningSup_eq_rawSup_nonneg X u ω).1]
    letI : Nonempty (Set.Icc (0 : ℝ≥0) s) :=
      ⟨⟨0, ⟨le_rfl, (zero_le : (0 : ℝ≥0) ≤ s)⟩⟩⟩
    refine ciSup_le fun v => ?_
    exact le_ciSup (hpath u)
      ⟨v.1, ⟨v.2.1, v.2.2.trans hsu⟩⟩
  have hdom (u : ℝ≥0) : X.X u ω ≤ runningSup X u ω := by
    rw [(runningSup_eq_rawSup_nonneg X u ω).1]
    exact le_ciSup (hpath u)
      ⟨u, ⟨(zero_le : (0 : ℝ≥0) ≤ u), le_rfl⟩⟩
  have hrepr (u : ℝ≥0) :
      runningSup X u ω =
        ⨆ s : Set.Icc (0 : ℝ≥0) u, X.X s.1 ω :=
    (runningSup_eq_rawSup_nonneg X u ω).1
  have hcontM :
      ContinuousWithinAt (fun u => runningSup X u ω) (Ici t) t :=
    runningSup_right_continuous_of_right_continuous
      (fun u => X.X u ω) (fun u => runningSup X u ω)
      hmonoM hdom hrepr (fun u => X.rightCont ω u) t
  have hmonoE : Monotone (fun u => E u ω) := by
    intro s u hsu
    dsimp [E]
    apply max_le_max
    · exact le_rfl
    · simpa [add_comm] using add_le_add_left (hmonoM hsu) (x - a)
  have hcontE :
      ContinuousWithinAt (fun u => E u ω) (Ici t) t := by
    dsimp [E]
    exact continuousWithinAt_const.max
      (continuousWithinAt_const.add hcontM)
  have hrE : rightLimit E t ω = E t ω :=
    rightLimit_eq_of_monotone_right_continuous E ω t hmonoE hcontE
  have hrl :
      rightLimit (barrierStrategy X x a) t ω = rightLimit E t ω := by
    unfold rightLimit
    refine iInf_congr (fun s => ?_)
    have hs0 : (s.1 : ℝ≥0) ≠ 0 :=
      ne_of_gt (lt_of_le_of_lt
        (zero_le : (0 : ℝ≥0) ≤ t) s.2)
    dsimp [E]
    simp only [barrierStrategy, hs0, if_false]
    rw [← (runningSup_eq_rawSup_nonneg X s.1 ω).1]
  have hM0 : runningSup X 0 ω = 0 := by
    rw [(runningSup_eq_rawSup_nonneg X 0 ω).1]
    rw [ciSup_subsingleton
      (i := (⟨0, by simp⟩ : Set.Icc (0 : ℝ≥0) 0))]
    simpa using X.X_zero ω
  rw [hrl, hrE]
  by_cases ht0 : t = 0
  · subst t
    dsimp [E]
    rw [hM0]
    simp [barrierStrategy]
  · have hDt : barrierStrategy X x a t ω = E t ω := by
      dsimp [E]
      simp only [barrierStrategy, ht0, if_false]
      rw [← (runningSup_eq_rawSup_nonneg X t ω).1]
    rw [hDt]
    simp [ht0]
