-- Prove2me | solution 1 for AvramDividend.Classical.named_killed_upcrossing_lower_of_raw_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:50:24.355432+00:00
-- url     : https://prove2.me/submissions/bf19b63f-6b78-4200-89d0-a26748623c61

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_firstUpcrossing_weighted_sandwich
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum

set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
/-! Convert the generic finite first-upcrossing survival bound to the named clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (w : Ω → ℝ≥0∞) (k : ℝ≥0∞)
    (hRaw : (∫⁻ ω,
      if twoSidedExitUpTime X b ω ≠ ∞ ∧
          (∀ t : ℝ≥0, t < (twoSidedExitUpTime X b ω).toNNReal →
            b - a ≤ X.X t ω)
      then w ω else 0 ∂P) = k) :
    k ≤ (∫⁻ ω,
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω
      then w ω else 0 ∂P) := by
  classical
  let u : Ω → ℝ≥0 := fun ω => (twoSidedExitUpTime X b ω).toNNReal
  let G : Set Ω := {ω | twoSidedExitUpTime X b ω ≠ ∞}
  have hu : ∀ ω ∈ G, (u ω : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) := by
    intro ω hG
    have hf : twoSidedExitUpTime X b ω ≠ ∞ := hG
    calc
      (u ω : ℝ≥0∞) = twoSidedExitUpTime X b ω := by
        simpa only [u] using ENNReal.coe_toNNReal hf
      _ = _ := chat08_named_upper_clock_eq_raw_infimum X b ω
  have hBound :=
    (killed_firstUpcrossing_weighted_sandwich
      X a b ha hb u G hu w).1
  have hEq : (∫⁻ ω,
      if ω ∈ G ∧ (u ω : ℝ≥0∞) < barrierRuinTime X a ω
      then w ω else 0 ∂P) =
      (∫⁻ ω,
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω
      then w ω else 0 ∂P) := by
    apply lintegral_congr_ae
    filter_upwards [] with ω
    by_cases hf : twoSidedExitUpTime X b ω ≠ ∞
    · have hG : ω ∈ G := hf
      have hcoe : (u ω : ℝ≥0∞) = twoSidedExitUpTime X b ω := by
        simpa only [u] using ENNReal.coe_toNNReal hf
      simp only [hG, true_and, hcoe]
    · have ht : twoSidedExitUpTime X b ω = ∞ := by
        simpa using hf
      have hnotG : ¬ ω ∈ G := by
        simp [G, ht]
      have hnotUp : ¬ twoSidedExitUpTime X b ω <
          barrierRuinTime X a ω := by
        rw [ht]
        exact not_lt_of_ge le_top
      simp only [hnotG, false_and, ite_false, hnotUp]
  calc
    k = (∫⁻ ω,
        if ω ∈ G ∧
            (∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω)
        then w ω else 0 ∂P) := by
      simpa only [G, u, Set.mem_setOf_eq] using hRaw.symm
    _ ≤ (∫⁻ ω,
        if ω ∈ G ∧
            (u ω : ℝ≥0∞) < barrierRuinTime X a ω
        then w ω else 0 ∂P) := by
      convert hBound using 1 <;>
        (apply lintegral_congr_ae; filter_upwards [] with ω; split_ifs <;> rfl)
    _ = _ := hEq
