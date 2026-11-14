-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:36:04.128009+00:00
-- url     : https://prove2.me/submissions/ee62dfbb-bbba-4d62-8b08-552f0f0f0fe2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The proved genuine compensated finite negative-band support is the same band filter of all physical jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) (n : ℕ)
    (F : Finset ℝ≥0)
    (hF : ∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
      (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν) =
      ∑ u ∈ F,
        if -1 < X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
           X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
             -(1 / ((n : ℝ) + 1))
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0 := by
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let N : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u)))
  let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) t ×ˢ
    Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  obtain ⟨G, hG, hGsum⟩ :=
    avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
      X ω t n
  have hFilter : G = F.filter
      (fun u => -1 < j u ∧ j u ≤ -(1 / ((n : ℝ) + 1))) := by
    ext u
    constructor
    · intro hu
      have hs := (hG u).mp hu
      have hj : j u ≠ 0 := by
        intro hz
        have hbound : j u ≤ -(1 / ((n : ℝ) + 1)) := hs.2.2.2
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact Finset.mem_filter.mpr
        ⟨(hF u).mpr ⟨hs.1, hs.2.1, hj⟩, hs.2.2⟩
    · intro hu
      obtain ⟨huf, hum⟩ := Finset.mem_filter.mp hu
      have hs := (hF u).mp huf
      exact (hG u).mpr ⟨hs.1, hs.2.1, hum⟩
  calc
    _ = ∫ p in E, p.2 ∂N := by
      dsimp [avram_p4_h_gaussian_intrinsic_small_band_compensated, E, N, j]
      ring
    _ = ∑ u ∈ G, j u := hGsum
    _ = ∑ u ∈ F.filter
          (fun u => -1 < j u ∧ j u ≤ -(1 / ((n : ℝ) + 1))), j u := by
        rw [hFilter]
    _ = ∑ u ∈ F, if -1 < j u ∧ j u ≤ -(1 / ((n : ℝ) + 1))
          then j u else 0 := by
        simp only [Finset.sum_filter]
