-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_reflected_record_survival_concat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T01:03:00.842713+00:00
-- url     : https://prove2.me/submissions/69da815f-58e3-4aeb-9ac7-df8c6af2d07f

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Killed reflected survival through two attained records is exactly the
    first-record survival and post-record shifted drawdown survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ω : Ω) (u T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hNext : ((u + T : ℝ≥0) : ℝ≥0∞) =
      twoSidedExitUpTime X (b + c) ω)
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Icc 0 u)) :
    (((u + T : ℝ≥0) : ℝ≥0∞) < barrierRuinTime X a ω) ↔
      ((u : ℝ≥0∞) < barrierRuinTime X a ω ∧
        ∀ t : ℝ≥0, t < T →
          sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) -
            X.X (u + t) ω ≤ a) := by
  have hbNext : 0 ≤ b + c := add_nonneg hb hc
  have hOld := firstUpcrossing_before_barrierRuin_iff_prefix_survival
    X a b ha hb ω u hu
  have hNew := firstUpcrossing_before_barrierRuin_iff_prefix_survival
    X a (b + c) ha hbNext ω (u + T) hNext
  have hReset := firstRecord_drawdown_post_shift_reset
    X b hb ω u hu hBdd
  constructor
  · intro hBeforeNext
    have hPrefix : ∀ r : ℝ≥0, r < u + T →
        reflectedSup X r ω ≤ a := hNew.mp hBeforeNext
    constructor
    · apply hOld.mpr
      intro r hr
      exact hPrefix r (lt_of_lt_of_le hr
        (le_add_of_nonneg_right (by exact zero_le)))
    · intro t ht
      have hUT : u + t < u + T := by
        simpa only [add_comm] using (add_lt_add_left ht u)
      have hAt := hPrefix (u + t) hUT
      change runningSup X (u + t) ω - X.X (u + t) ω ≤ a at hAt
      rwa [hReset t] at hAt
  · rintro ⟨hBeforeFirst, hAfter⟩
    apply hNew.mpr
    intro r hr
    by_cases hru : r < u
    · exact (hOld.mp hBeforeFirst) r hru
    · have hur : u ≤ r := le_of_not_gt hru
      have hEq : u + (r - u) = r := add_tsub_cancel_of_le hur
      have ht : r - u < T := by
        have hShift : u + (r - u) < u + T := by
          simpa only [hEq] using hr
        exact (add_lt_add_iff_left u).mp hShift
      have hPost : reflectedSup X (u + (r - u)) ω ≤ a := by
        change runningSup X (u + (r - u)) ω -
          X.X (u + (r - u)) ω ≤ a
        rw [hReset (r - u)]
        exact hAfter (r - u) ht
      simpa only [hEq] using hPost
