-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_all_negative_marks_exhausted_by_threshold_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:27:12.994087+00:00
-- url     : https://prove2.me/submissions/0f5fdc2e-e219-41eb-ab61-1df26d81369e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original Lévy jump count on all negative marks is the
monotone supremum of finite-threshold negative mark-band counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) =
    ⨆ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ {z : ℝ |
          z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}) := by
  let B : ℕ → Set ℝ := fun n =>
    {z : ℝ | z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}
  have hMon : Monotone B := by
    intro n m hnm z hz
    refine ⟨hz.1, ?_⟩
    have hm : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hRec : (1 : ℝ) / ((m : ℝ) + 1) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hm
    exact hRec.trans hz.2
  have hUnion : (⋃ n, B n) = Iio (0 : ℝ) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact hn.1
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < -z by linarith)
      exact ⟨n, hz, le_of_lt hn⟩
  simpa only [hUnion] using
    avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands
      X s t B hMon ω
