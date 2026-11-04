-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_negative_subset_threshold_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:35:48.669931+00:00
-- url     : https://prove2.me/submissions/3dafc26e-858f-4cbd-bcb5-996cbe0bec93

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every negative-support original marked-jump count exhausts by the
original path counts restricted to marks bounded away from zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (hNeg : B ⊆ Iio (0 : ℝ)) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    ⨆ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ {z : ℝ |
          z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z})) := by
  let C : ℕ → Set ℝ := fun n => B ∩
    {z : ℝ | z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}
  have hMon : Monotone C := by
    intro n m hnm z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    have hm : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hRec : (1 : ℝ) / ((m : ℝ) + 1) ≤
        1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hm
    exact hRec.trans hz.2.2
  have hUnion : (⋃ n, C n) = B := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hz, -⟩
      exact hz
    · intro hz
      have hzNeg : z < 0 := hNeg hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < -z by linarith)
      exact ⟨n, hz, hzNeg, le_of_lt hn⟩
  simpa only [hUnion] using
    avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands
      X s t C hMon ω
