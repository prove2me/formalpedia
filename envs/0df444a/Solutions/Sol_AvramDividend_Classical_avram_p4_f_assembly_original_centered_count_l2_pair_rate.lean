-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_centered_count_l2_pair_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:13:24.018952+00:00
-- url     : https://prove2.me/submissions/96333c3a-1d2b-4fc2-9e54-490622fb22ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_second_moment_ordered_pairs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
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
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable J P →
    (∫ ω, J ω ∂P) = r →
    Integrable (fun ω => 2 * (K ω : ℝ)) P →
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 →
    Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = r := by
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
  let r : ℝ :=
    (((T : ℝ≥0) : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable J P →
    (∫ ω, J ω ∂P) = r →
    Integrable (fun ω => 2 * (K ω : ℝ)) P →
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 →
    Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = r
  intro hJ hJmean hK hKmean
  obtain ⟨hJ2Iff, hJ2Eq⟩ :=
    avram_p4_f_assembly_original_second_moment_ordered_pairs X T n hJ
  have hJ2 : Integrable (fun ω => (J ω) ^ 2) P := hJ2Iff.mpr hK
  have hCross : Integrable (fun ω => (2 * r) * J ω) P :=
    hJ.const_mul _
  have hConst : Integrable (fun _ : Ω => r ^ 2) P :=
    integrable_const _
  have hExpand : (fun ω : Ω => (J ω - r) ^ 2) =
      (fun ω : Ω => (J ω) ^ 2 - (2 * r) * J ω + r ^ 2) := by
    funext ω
    ring
  have hSq : Integrable (fun ω => (J ω - r) ^ 2) P := by
    rw [hExpand]
    exact (hJ2.sub hCross).add hConst
  have hIntAdd :
      (∫ ω, (J ω) ^ 2 - (2 * r) * J ω + r ^ 2 ∂P) =
      (∫ ω, (J ω) ^ 2 - (2 * r) * J ω ∂P) +
      (∫ _ : Ω, r ^ 2 ∂P) :=
    integral_add (hJ2.sub hCross) hConst
  have hIntSub :
      (∫ ω, (J ω) ^ 2 - (2 * r) * J ω ∂P) =
      (∫ ω, (J ω) ^ 2 ∂P) -
      (∫ ω, (2 * r) * J ω ∂P) :=
    integral_sub hJ2 hCross
  have hIntMul :
      (∫ ω, (2 * r) * J ω ∂P) =
      (2 * r) * (∫ ω, J ω ∂P) := by
    rw [integral_const_mul]
  have hIntConst : (∫ _ : Ω, r ^ 2 ∂P) = r ^ 2 := by simp
  constructor
  · exact hSq
  · calc
      (∫ ω, (J ω - r) ^ 2 ∂P)
          = (∫ ω, (J ω) ^ 2 - (2 * r) * J ω + r ^ 2 ∂P) := by
              rw [hExpand]
      _ = (∫ ω, (J ω) ^ 2 ∂P) -
            (2 * r) * (∫ ω, J ω ∂P) + r ^ 2 := by
              rw [hIntAdd, hIntSub, hIntMul, hIntConst]
      _ = r := by
        rw [hJ2Eq, integral_add hJ hK, hJmean, hKmean]
        ring
