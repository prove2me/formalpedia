-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_first_record_survival_iff_height_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:28:20.609973+00:00
-- url     : https://prove2.me/submissions/8c29a205-0882-428a-8140-9c50fa60befb

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Source first-record survival is the true reflected prefix maximum bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω) :
    (u : ℝ≥0∞) < barrierRuinTime X a ω ↔
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) ≤ a := by
  let R : ℝ≥0 → ℝ := fun t => reflectedSup X t ω
  let S : Set ℝ := R '' Icc 0 u
  have hNonempty : S.Nonempty := ⟨R 0, ⟨0, by simp, rfl⟩⟩
  have hUSC : UpperSemicontinuousOn R (Icc 0 u) :=
    reflectedSup_upperSemicontinuousOn_Icc X ω u
  have hIcc : (Icc (0 : ℝ≥0) u).Nonempty := ⟨0, by simp⟩
  obtain ⟨v, hv, hmax⟩ :=
    UpperSemicontinuousOn.exists_isMaxOn hIcc isCompact_Icc hUSC
  have hBdd : BddAbove S := by
    refine ⟨R v, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact hmax ht
  have hzero : R u = 0 := by
    exact firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u
      (by simpa only [twoSidedExitUpTime] using hu)
  have hprefix := firstUpcrossing_before_barrierRuin_iff_prefix_survival
    X a b ha hb ω u (by simpa only [twoSidedExitUpTime] using hu)
  change (u : ℝ≥0∞) < barrierRuinTime X a ω ↔ sSup S ≤ a
  constructor
  · intro h
    apply csSup_le hNonempty
    rintro y ⟨t, ht, rfl⟩
    by_cases hlt : t < u
    · exact hprefix.mp h t hlt
    · have heq : t = u := le_antisymm ht.2 (le_of_not_gt hlt)
      subst t
      rw [hzero]
      exact ha.le
  · intro h
    apply hprefix.mpr
    intro t ht
    apply le_trans (le_csSup hBdd ?_) h
    exact ⟨t, ⟨by positivity, le_of_lt ht⟩, rfl⟩
