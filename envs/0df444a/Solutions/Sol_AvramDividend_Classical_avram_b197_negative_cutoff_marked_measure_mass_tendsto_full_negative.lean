-- Prove2me | solution 1 for AvramDividend.Classical.avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:30:19.851536+00:00
-- url     : https://prove2.me/submissions/0ed2f439-4eff-4433-a070-654e07332bf6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any marked source measure charges the full negative rectangle as the limit of increasing reciprocal negative cutoff rectangle masses. -/
theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      μ (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))))
      atTop (𝓝 (μ (Ioc 0 T ×ˢ Iio (0 : ℝ)))) := by
  let S : ℕ → Set (ℝ≥0 × ℝ) := fun n =>
    Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))
  have hMono : Monotone S := by
    intro n m hnm z hz
    have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hCut :
        -(1 / ((n : ℝ) + 1)) ≤ -(1 / ((m : ℝ) + 1)) := by
      gcongr
    exact ⟨hz.1, le_trans hz.2 hCut⟩
  have hUnion : (⋃ n : ℕ, S n) =
      Ioc 0 T ×ˢ (⋃ n : ℕ, Iic (-(1 / ((n : ℝ) + 1)))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact ⟨hn.1, Set.mem_iUnion.mpr ⟨n, hn.2⟩⟩
    · rintro ⟨ht, hband⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hband
      exact Set.mem_iUnion.mpr ⟨n, ⟨ht, hn⟩⟩
  rw [avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks] at hUnion
  have h := MeasureTheory.tendsto_measure_iUnion_atTop (μ := μ) hMono
  simpa only [Function.comp_def, S, hUnion] using h
