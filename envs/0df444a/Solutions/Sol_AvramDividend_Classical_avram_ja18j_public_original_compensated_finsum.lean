-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18j_public_original_compensated_finsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:42:18.170486+00:00
-- url     : https://prove2.me/submissions/fca6995b-f342-462d-b46d-8aa4f6867935

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Public, source-faithful finite-band marked jump sum with the
original same-path source compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (T : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω =
        (∑ u ∈ F, j u) -
          (T : ℝ) * (∫ z in Ioc (-1 : ℝ)
            (-(1 / ((n : ℝ) + 1))), z ∂X.ν) := by
  classical
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let N : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u)))
  let E : Set (ℝ≥0 × ℝ) :=
    Ioc (0 : ℝ≥0) T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  obtain ⟨F, hF, hEq⟩ :=
    avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
      X ω T n
  refine ⟨F, hF, ?_⟩
  change (∫ p in E, p.2 ∂N) -
    (T : ℝ) * (∫ z in Ioc (-1 : ℝ)
      (-(1 / ((n : ℝ) + 1))), z ∂X.ν) =
    (∑ u ∈ F, j u) -
      (T : ℝ) * (∫ z in Ioc (-1 : ℝ)
        (-(1 / ((n : ℝ) + 1))), z ∂X.ν)
  rw [hEq]
