-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:21:26.026112+00:00
-- url     : https://prove2.me/submissions/af3cbed9-8825-4a91-88a2-1012f0659f83

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_initial_dividendMeasure_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Stieltjes barrier payments vanish on the entire initial closed time window. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (dividendMeasure (barrierStrategy X x a) ω)
      (Set.Icc (0 : ℝ) (u : ℝ)) = 0 := by
  let μ := dividendMeasure (barrierStrategy X x a) ω
  have hZero : μ ({0} : Set ℝ) = 0 :=
    barrierStrategy_no_initial_dividendMeasure_atom
      X x a hx0 (le_trans hx0 hxa) hxa ω
  have hWindow : μ (Set.Ioc (0 : ℝ) (u : ℝ)) = 0 :=
    barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
      X x a hx0 hxa ω u hu
  have hsub : Set.Icc (0 : ℝ) (u : ℝ) ⊆
      ({0} : Set ℝ) ∪ Set.Ioc 0 (u : ℝ) := by
    intro t ht
    rcases lt_or_eq_of_le ht.1 with hlt | heq
    · exact Or.inr ⟨hlt, ht.2⟩
    · exact Or.inl heq.symm
  have hle : μ (Set.Icc (0 : ℝ) (u : ℝ)) ≤ 0 := by
    calc
      μ (Set.Icc (0 : ℝ) (u : ℝ)) ≤
          μ (({0} : Set ℝ) ∪ Set.Ioc 0 (u : ℝ)) :=
        measure_mono hsub
      _ ≤ μ ({0} : Set ℝ) + μ (Set.Ioc 0 (u : ℝ)) :=
        measure_union_le _ _
      _ = 0 := by rw [hZero, hWindow]; simp
  exact le_antisymm hle (by exact zero_le)
