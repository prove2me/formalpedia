-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja25_original_marked_strip_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:00:54.668001+00:00
-- url     : https://prove2.me/submissions/889c5399-d897-467e-82f2-caef13f9e288

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_smallband_compensator_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_strip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original compensated strip inherits L2 from its two source-exact cutoff sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
      Integrable (fun ω => (C ω) ^ 2) P := by
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
  change Integrable (fun ω => (C ω) ^ 2) P
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
  convert hdiff using 1
  funext ω
  rw [hbridge ω]
