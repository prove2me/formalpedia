-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_source_factorial_L1_pair_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:05:43.29407+00:00
-- url     : https://prove2.me/submissions/95848e09-d7e3-45b5-8caa-4ddd474868ef

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
    (Integrable (fun ω => J ω * (J ω - 1)) P ↔
      Integrable (fun ω => 2 * (K ω : ℝ)) P) ∧
    (∫ ω, J ω * (J ω - 1) ∂P) =
      (∫ ω, 2 * (K ω : ℝ) ∂P) := by
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
  change (Integrable (fun ω => J ω * (J ω - 1)) P ↔
    Integrable (fun ω => 2 * (K ω : ℝ)) P) ∧
    (∫ ω, J ω * (J ω - 1) ∂P) =
      (∫ ω, 2 * (K ω : ℝ) ∂P)
  have hFun :
      (fun ω : Ω => J ω * (J ω - 1)) =
      (fun ω : Ω => 2 * (K ω : ℝ)) := by
    funext ω
    exact avram_p4_f_assembly_original_negative_band_real_factorial_pair X ω T n
  rw [hFun]
  exact ⟨Iff.rfl, rfl⟩
