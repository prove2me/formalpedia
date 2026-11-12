-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18u_original_largejump_sum_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:52:38.205796+00:00
-- url     : https://prove2.me/submissions/e10b3594-1893-4045-884c-a068487e682c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Original nonpositive jumps accumulate monotonically in the large band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (ω : Ω) (s t : ℝ≥0), s ≤ t →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ≤
      avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω := by
  intro ω s t hst
  let j : ℝ≥0 → ℝ :=
    fun u => X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  obtain ⟨Fs, hs, hEs⟩ :=
    avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
      X ω s
  obtain ⟨Ft, ht, hEt⟩ :=
    avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
      X ω t
  have hSubset : Fs ⊆ Ft := by
    intro u hu
    obtain ⟨hpos, hus, hmark⟩ := (hs u).mp hu
    exact (ht u).mpr ⟨hpos, hus.trans hst, hmark⟩
  have hNeg : ∀ u ∈ Ft, 0 ≤ -j u := by
    intro u hu
    have hj : j u ≤ -1 := ((ht u).mp hu).2.2
    linarith
  have hSum :
      (∑ u ∈ Fs, -j u) ≤ (∑ u ∈ Ft, -j u) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun u hu _ => hNeg u hu)
  have hMinus := neg_le_neg hSum
  rw [hEt, hEs]
  simpa only [Finset.sum_neg_distrib, neg_neg] using hMinus
