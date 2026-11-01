-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_finite_horizon_atom_support_eq_right_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:42:30.446279+00:00
-- url     : https://prove2.me/submissions/0e7ecc95-90f6-49d1-908a-8fd0965064a3

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option maxHeartbeats 1000000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    {s : ℝ | μ {s} ≠ 0} =
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
        0 < rightLimit D s.toNNReal ω - D s.toNNReal ω} := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  have hInside (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) :
      μ {s} =
        ENNReal.ofReal (rightLimit D s.toNNReal ω - D s.toNNReal ω) := by
    have hcoe : (s.toNNReal : ℝ) = s :=
      Real.coe_toNNReal s hs.1
    calc
      μ {s} = (dividendMeasure D ω) {s} := by
        simp [μ, hs]
      _ = ENNReal.ofReal (rightLimit D s.toNNReal ω - D s.toNNReal ω) := by
        simpa only [hcoe] using
          (dividendMeasure_singleton_eq_rightLimit_sub D hD ω s.toNNReal)
  change {s : ℝ | μ {s} ≠ 0} =
    {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
  ext s
  constructor
  · intro hs
    change μ {s} ≠ 0 at hs
    have hmem : s ∈ Icc (0 : ℝ) (T : ℝ) := by
      by_contra hnot
      have hzero : μ {s} = 0 := by
        simp [μ, hnot]
      exact hs hzero
    have hnonzero :
        ENNReal.ofReal (rightLimit D s.toNNReal ω -
          D s.toNNReal ω) ≠ 0 := by
      simpa only [hInside s hmem] using hs
    exact ⟨hmem.1, hmem.2,
      ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hnonzero)⟩
  · rintro ⟨hs0, hsT, hpos⟩
    have hmem : s ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hs0, hsT⟩
    change μ {s} ≠ 0
    rw [hInside s hmem]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
