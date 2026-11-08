-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_turn8_random_zero_lump_dividend_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:36:44.157869+00:00
-- url     : https://prove2.me/submissions/9dd6a064-329c-4fef-af66-563738952f85

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A nonnegative dividend amount revealed by the initial filtration can be
    paid as an immediate right jump while retaining the exact left-continuous
    adapted dividend-strategy convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (L : Ω → ℝ)
    (hL : ∀ ω, 0 ≤ L ω)
    (hLadapt : ∀ t : ℝ≥0, 0 < t → Measurable[𝓕 t] L) :
    IsDividendStrategy 𝓕
      (fun t ω => if t = 0 then 0 else L ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    simp
  · intro ω a b hab
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · subst b
        simp
      · simpa [hb] using hL ω
    · have hb : b ≠ 0 := by
        intro hzero
        apply ha
        exact le_antisymm (hzero ▸ hab) zero_le
      simp [ha, hb]
  · intro ω t
    by_cases ht : t = 0
    · subst t
      have hIic : Iic (0 : ℝ≥0) = {(0 : ℝ≥0)} := by
        ext s
        change s ≤ 0 ↔ s = 0
        constructor
        · intro hs
          exact le_antisymm hs zero_le
        · intro hs
          rw [hs]
      rw [hIic]
      exact continuousWithinAt_singleton
    · have hpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht
      have hne : ∀ᶠ s : ℝ≥0 in 𝓝[Iic t] t, s ≠ 0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (isOpen_Ioi.mem_nhds hpos)] with s hs
        exact ne_of_gt hs
      refine ContinuousWithinAt.congr_of_eventuallyEq
        (show ContinuousWithinAt (fun _ : ℝ≥0 => L ω) (Iic t) t
          from continuousWithinAt_const) ?_ ?_
      · filter_upwards [hne] with s hs
        simp [hs]
      · simp [ht]
  · intro t
    by_cases ht : t = 0
    · subst t
      simpa using
        (measurable_const : Measurable[𝓕 (0 : ℝ≥0)]
          (fun _ : Ω => (0 : ℝ)))
    · have hpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht
      simpa [ht] using hLadapt t hpos
