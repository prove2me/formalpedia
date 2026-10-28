-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_weight_lower_of_strict_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:12:58.439875+00:00
-- url     : https://prove2.me/submissions/03b93513-793f-4ce2-b019-b4d9872b97b2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_strict_up_before_down_preserves_lower_prefix
import Theorems.Thm_AvramDividend_Classical_named_killed_upcrossing_lower_of_raw_exit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-! A successful ordinary two-sided exit is a surviving reflected record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (w : Ω → ℝ≥0∞) (k : ℝ≥0∞)
    (hExit : (∫⁻ ω,
      if twoSidedExitUpTime X b ω <
          twoSidedExitDownTime X (b - a) ω
      then w ω else 0 ∂P) = k) :
    k ≤ (∫⁻ ω,
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω
      then w ω else 0 ∂P) := by
  have hEvent (ω : Ω)
      (hUp : twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X (b - a) ω) :
      twoSidedExitUpTime X b ω ≠ ∞ ∧
      (∀ t : ℝ≥0, t < (twoSidedExitUpTime X b ω).toNNReal →
        b - a ≤ X.X t ω) := by
    have hf : twoSidedExitUpTime X b ω ≠ ∞ :=
      ne_top_of_lt (lt_of_lt_of_le hUp le_top)
    refine ⟨hf, ?_⟩
    intro t ht
    apply strict_up_before_down_preserves_lower_prefix
      X b (b - a) ω hUp t
    calc
      (t : ℝ≥0∞) <
          ((twoSidedExitUpTime X b ω).toNNReal : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.mpr ht
      _ = twoSidedExitUpTime X b ω := ENNReal.coe_toNNReal hf
  have hMon :
      (∫⁻ ω,
        if twoSidedExitUpTime X b ω <
            twoSidedExitDownTime X (b - a) ω
        then w ω else 0 ∂P) ≤
      (∫⁻ ω,
        if twoSidedExitUpTime X b ω ≠ ∞ ∧
            (∀ t : ℝ≥0,
              t < (twoSidedExitUpTime X b ω).toNNReal →
              b - a ≤ X.X t ω)
        then w ω else 0 ∂P) := by
    apply lintegral_mono
    intro ω
    by_cases h : twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X (b - a) ω
    · have he := hEvent ω h
      simp only [if_pos h, if_pos he, le_refl]
    · simp only [if_neg h, zero_le]
  calc
    k = (∫⁻ ω,
      if twoSidedExitUpTime X b ω <
          twoSidedExitDownTime X (b - a) ω
      then w ω else 0 ∂P) := hExit.symm
    _ ≤ (∫⁻ ω,
      if twoSidedExitUpTime X b ω ≠ ∞ ∧
          (∀ t : ℝ≥0, t < (twoSidedExitUpTime X b ω).toNNReal →
            b - a ≤ X.X t ω)
      then w ω else 0 ∂P) := hMon
    _ ≤ (∫⁻ ω,
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω
      then w ω else 0 ∂P) :=
      named_killed_upcrossing_lower_of_raw_exit
        X a b ha hb w _ rfl
