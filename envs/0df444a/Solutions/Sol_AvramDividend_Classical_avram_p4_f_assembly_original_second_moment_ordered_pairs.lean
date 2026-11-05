-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_second_moment_ordered_pairs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:13:13.522055+00:00
-- url     : https://prove2.me/submissions/468d1dbc-cf4e-4d79-94e4-95e5aaa553d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_real_factorial_pair
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    Integrable J P →
    (Integrable (fun ω => (J ω) ^ 2) P ↔
      Integrable (fun ω => 2 * (K ω : ℝ)) P) ∧
    (∫ ω, (J ω) ^ 2 ∂P) =
      (∫ ω, J ω + 2 * (K ω : ℝ) ∂P) := by
  classical
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let J : Ω → ℝ := fun ω =>
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let K : Ω → ℕ := fun ω =>
    ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
  change Integrable J P →
    (Integrable (fun ω => (J ω) ^ 2) P ↔
      Integrable (fun ω => 2 * (K ω : ℝ)) P) ∧
    (∫ ω, (J ω) ^ 2 ∂P) =
      (∫ ω, J ω + 2 * (K ω : ℝ) ∂P)
  intro hJ
  have hPair : ∀ ω : Ω, J ω * (J ω - 1) = 2 * (K ω : ℝ) :=
    fun ω => avram_p4_f_assembly_original_negative_band_real_factorial_pair X ω T n
  have hSum : (fun ω : Ω => (J ω) ^ 2) =
      (fun ω : Ω => J ω + 2 * (K ω : ℝ)) := by
    funext ω
    nlinarith [hPair ω]
  have hDiff : (fun ω : Ω => 2 * (K ω : ℝ)) =
      (fun ω : Ω => (J ω) ^ 2 - J ω) := by
    funext ω
    nlinarith [hPair ω]
  constructor
  · constructor
    · intro h2
      rw [hDiff]
      exact h2.sub hJ
    · intro hK
      rw [hSum]
      exact hJ.add hK
  · rw [hSum]
