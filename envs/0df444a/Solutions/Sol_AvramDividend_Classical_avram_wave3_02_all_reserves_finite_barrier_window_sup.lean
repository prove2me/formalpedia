-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_reserves_finite_barrier_window_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:58:29.302007+00:00
-- url     : https://prove2.me/submissions/abed0bd8-1b30-4209-867f-8de166a50872

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_reserve_high_barrier_value_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- From every nonnegative reserve, including zero, the genuine
constant-barrier dividend class has a finite supremum search interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    ∃ A : ℝ, 0 ≤ A ∧
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) =
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) := by
  classical
  let f : ℝ → ENNReal := fun a => dividendValue X q x (barrierStrategy X x a)
  have hlim : Tendsto f atTop (𝓝 (0 : ENNReal)) := by
    exact avram_wave3_02_all_reserve_high_barrier_value_zero X hX q hq W hW x hx
  by_cases hpositive : ∃ b : ℝ, 0 ≤ b ∧ 0 < f b
  · obtain ⟨b, hb0, hbpos⟩ := hpositive
    have hevent : ∀ᶠ a : ℝ in atTop, f a < f b :=
      Filter.Tendsto.eventually_lt_const hbpos hlim
    obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 hevent
    let B : ℝ := max A (max b 0)
    have hB : 0 ≤ B := (le_max_right b 0).trans (le_max_right A (max b 0))
    have hbB : b ≤ B := (le_max_left b 0).trans (le_max_right A (max b 0))
    have hbase : f b ≤
        (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ B), f a) :=
      le_iSup_of_le b (le_iSup_of_le ⟨hb0, hbB⟩ (le_refl _))
    refine ⟨B, hB, ?_⟩
    apply le_antisymm
    · refine iSup_le fun a => ?_
      refine iSup_le fun ha => ?_
      by_cases hab : a ≤ B
      · exact le_iSup_of_le a (le_iSup_of_le ⟨ha, hab⟩ (le_refl _))
      · have hAa : A ≤ a :=
          (le_max_left A (max b 0)).trans (le_of_lt (lt_of_not_ge hab))
        exact (le_of_lt (hA a hAa)).trans hbase
    · refine iSup_le fun a => ?_
      refine iSup_le fun ha => ?_
      exact le_iSup_of_le a (le_iSup_of_le ha.1 (le_refl _))
  · have hzero : ∀ a : ℝ, 0 ≤ a → f a = 0 := by
      intro a ha
      apply le_antisymm
      · exact le_of_not_gt (by
          intro hpos
          exact hpositive ⟨a, ha, hpos⟩)
      · exact zero_le
    refine ⟨0, le_refl (0 : ℝ), ?_⟩
    apply le_antisymm
    · refine iSup_le fun a => ?_
      refine iSup_le fun ha => ?_
      have hz : dividendValue X q x (barrierStrategy X x a) = 0 := hzero a ha
      rw [hz]
      exact bot_le
    · refine iSup_le fun a => ?_
      refine iSup_le fun ha => ?_
      exact le_iSup_of_le a (le_iSup_of_le ha.1 (le_refl _))
