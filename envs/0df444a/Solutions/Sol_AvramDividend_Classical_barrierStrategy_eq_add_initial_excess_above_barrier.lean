-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:03:47.064399+00:00
-- url     : https://prove2.me/submissions/bb39d5e1-b26e-4d77-9ab9-2de2443838c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ha : 0 ≤ a) (hax : a < x) :
    barrierStrategy X x a =
      (fun t ω => if t = 0 then 0 else (x - a) + barrierStrategy X a a t ω) := by
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp [barrierStrategy]
  · have hbdd :
        BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => X.X s.1 ω)) := by
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
    have hsup0 :
        0 ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω := by
      calc
        0 = X.X 0 ω := (X.X_zero ω).symm
        _ ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω :=
          le_ciSup hbdd ⟨0, ⟨le_rfl, (zero_le : (0 : ℝ≥0) ≤ t)⟩⟩
    have hxa : 0 ≤ x - a := (sub_pos.mpr hax).le
    simp only [barrierStrategy, if_neg ht, sub_self, zero_add]
    rw [max_eq_right hsup0]
    rw [max_eq_right (add_nonneg hxa hsup0)]
