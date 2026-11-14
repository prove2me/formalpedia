-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:30:44.160729+00:00
-- url     : https://prove2.me/submissions/275ac216-d442-42f4-91f8-507a532cb101

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The already proved original physical large band finite support is the large-band filter of all source jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (F : Finset ℝ≥0)
    (hF : ∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      ∑ u ∈ F,
        if X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0 := by
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  obtain ⟨G, hG, hGsum⟩ :=
    avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum X ω t
  have hFilter : G = F.filter (fun u => j u ≤ -1) := by
    ext u
    constructor
    · intro hu
      have hs := (hG u).mp hu
      have hj : j u ≠ 0 := by
        intro hz
        have hbound : j u ≤ (-1 : ℝ) := hs.2.2
        linarith
      exact Finset.mem_filter.mpr
        ⟨(hF u).mpr ⟨hs.1, hs.2.1, hj⟩, hs.2.2⟩
    · intro hu
      obtain ⟨huf, hum⟩ := Finset.mem_filter.mp hu
      have hs := (hF u).mp huf
      exact (hG u).mpr ⟨hs.1, hs.2.1, hum⟩
  calc
    _ = ∑ u ∈ G, j u := hGsum
    _ = ∑ u ∈ F.filter (fun u => j u ≤ -1), j u := by rw [hFilter]
    _ = ∑ u ∈ F, if j u ≤ -1 then j u else 0 := by
      simp only [Finset.sum_filter]
