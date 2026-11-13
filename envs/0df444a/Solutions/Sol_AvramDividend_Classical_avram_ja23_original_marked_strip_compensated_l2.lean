-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja23_original_marked_strip_compensated_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:53:42.791023+00:00
-- url     : https://prove2.me/submissions/f35fe0aa-2e07-42d1-ad60-8e8c2910e707

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja24_original_marked_strip_second_moment_of_L2
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_smallband_compensator_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_strip
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact original marked strip L2: finite activity gives L2 and physical isometry gives its variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P ∧
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν) := by
  intro n m hnm t
  let S : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let C : Ω → ℝ := fun ω =>
    (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
      (t : ℝ) * (∫ z in S, z ∂X.ν)
  change Integrable (fun ω => (C ω) ^ 2) P ∧
    (∫ ω, (C ω) ^ 2 ∂P) =
      (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν)
  have hm : Measurable (fun ω =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω) :=
    (avram_anoise33_original_smallband_compensator_adapted
      X m t).mono (𝓕.le t) le_rfl
  have hn : Measurable (fun ω =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) :=
    (avram_anoise33_original_smallband_compensator_adapted
      X n t).mono (𝓕.le t) le_rfl
  have hdiff : Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2) P := by
    apply avram_ja19_square_integrable_of_ae_sum_components
      (fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω)
      (fun ω => -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
      (hm.sub hn).aestronglyMeasurable
      (avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
        X hFinite m t)
      (by simpa only [neg_sq] using
        (avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
          X hFinite n t))
    filter_upwards [] with ω
    ring
  have hbridge (ω : Ω) : C ω =
      avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by
    simpa [C, S, NX] using
      (avram_p4_h_gaussian_original_smalljump_cutoff_strip
        X n m hnm t ω).symm
  have hC : Integrable (fun ω => (C ω) ^ 2) P := by
    convert hdiff using 1
    funext ω
    rw [hbridge ω]
  exact ⟨hC,
    avram_ja24_original_marked_strip_second_moment_of_L2
      X hX hFinite n m hnm t hC⟩
