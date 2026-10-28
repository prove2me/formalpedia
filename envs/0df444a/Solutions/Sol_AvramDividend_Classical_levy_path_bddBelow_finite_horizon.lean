-- Prove2me | solution 1 for AvramDividend.Classical.levy_path_bddBelow_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:26:19.042192+00:00
-- url     : https://prove2.me/submissions/27943bd0-6998-434a-a5aa-04aab7da42b7

import Mathlib.Topology.Order.Bornology
import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-- Every càdlàg Lévy trajectory is bounded below on any finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) :
    BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by
  have hbdd : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => -(X.X s.1 ω))) := by
    refine one_sided_limits_bddAbove_Icc (fun u => -(X.X u ω)) ?_ ?_ t
    · intro u
      exact (X.rightCont ω u).neg
    · intro u
      by_cases hu : u = 0
      · subst u
        refine ⟨0, ?_⟩
        have hb : (𝓝[<] (0 : ℝ≥0)) = ⊥ :=
          nhdsLT_eq_bot_iff.mpr (.inl (fun v => (zero_le : (0 : ℝ≥0) ≤ v)))
        rw [hb]
        exact tendsto_bot
      · have hpos : 0 < u :=
          lt_of_le_of_ne ((zero_le : (0 : ℝ≥0) ≤ u)) (Ne.symm hu)
        obtain ⟨l, hl⟩ := X.leftLim ω u hpos
        exact ⟨-l, hl.neg⟩
  obtain ⟨b, hb⟩ := hbdd
  refine ⟨-b, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  have hneg : -(X.X s ω) ≤ b :=
    hb (Set.mem_range.mpr ⟨⟨s, ⟨zero_le, hs⟩⟩, rfl⟩)
  linarith
