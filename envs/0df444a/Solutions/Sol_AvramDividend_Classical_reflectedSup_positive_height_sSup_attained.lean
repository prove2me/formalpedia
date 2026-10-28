-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_positive_height_sSup_attained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:52:57.293678+00:00
-- url     : https://prove2.me/submissions/f8b58b34-df05-4d1c-81bf-1b98b6c10b97

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_positive_height_attained

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (hζ : 0 < ζ)
    (hEnd : reflectedSup X ζ ω = 0)
    (hPos : 0 < sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 ζ)) :
    ∃ T : ℝ≥0, 0 < T ∧ T < ζ ∧
      reflectedSup X T ω =
        sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 ζ) := by
  let R : ℝ≥0 → ℝ := fun t => reflectedSup X t ω
  have hUSC : UpperSemicontinuousOn R (Icc 0 ζ) :=
    reflectedSup_upperSemicontinuousOn_Icc X ω ζ
  have hBdd : BddAbove (R '' Icc (0 : ℝ≥0) ζ) :=
    UpperSemicontinuousOn.bddAbove_of_isCompact isCompact_Icc hUSC
  have hNonempty : (R '' Icc (0 : ℝ≥0) ζ).Nonempty := by
    refine ⟨R 0, 0, ?_, rfl⟩
    exact ⟨le_refl 0, le_of_lt hζ⟩
  have hBound : ∀ t : ℝ≥0, t ≤ ζ →
      R t ≤ sSup (R '' Icc (0 : ℝ≥0) ζ) := by
    intro t ht
    exact le_csSup hBdd ⟨t, ⟨(show (0 : ℝ≥0) ≤ t from zero_le), ht⟩, rfl⟩
  have hSharp : ∀ y : ℝ,
      y < sSup (R '' Icc (0 : ℝ≥0) ζ) →
      ∃ t : ℝ≥0, t ≤ ζ ∧ y < R t := by
    intro y hy
    obtain ⟨b, hb, hyb⟩ := (lt_csSup_iff hBdd hNonempty).mp hy
    rcases hb with ⟨t, ht, rfl⟩
    exact ⟨t, ht.2, hyb⟩
  exact reflectedSup_finite_positive_height_attained
    X ω ζ hζ hEnd
    (sSup (R '' Icc (0 : ℝ≥0) ζ)) hPos hBound hSharp
