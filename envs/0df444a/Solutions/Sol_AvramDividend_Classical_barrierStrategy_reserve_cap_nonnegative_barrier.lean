-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_reserve_cap_nonnegative_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:55:49.889147+00:00
-- url     : https://prove2.me/submissions/a8d2a066-3dda-4411-9d09-ea4984f24739

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
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    ∀ ω (t : ℝ≥0), 0 < t →
      ENNReal.ofReal (riskProcess X x (barrierStrategy X x a) t ω) ≤
        ENNReal.ofReal a := by
  intro ω t ht
  have hbdd :
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
  have hcur :
      X.X t ω ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω := by
    exact le_ciSup hbdd ⟨t, ⟨zero_le, le_rfl⟩⟩
  have hsum :
      x - a + X.X t ω ≤
        x - a + (⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω) := by
    linarith
  have hdiv :
      x - a + X.X t ω ≤ barrierStrategy X x a t ω := by
    simp only [barrierStrategy, ne_of_gt ht, if_false]
    exact hsum.trans (le_max_right _ _)
  have hrisk : riskProcess X x (barrierStrategy X x a) t ω ≤ a := by
    unfold riskProcess
    linarith
  exact ENNReal.ofReal_le_ofReal hrisk
