-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_smallband_finite_activity_pathwise_total_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:22:43.028375+00:00
-- url     : https://prove2.me/submissions/7e0e013a-84ec-4a4c-8f96-3f3d5e0dabf6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18j_public_original_compensated_finsum
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_negative_finsum_card_le_total_count
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_deterministic_compensator_mass_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0,
      let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))
      ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤
          (N ω).toReal + (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by
  intro T
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  have hraw :=
    avram_ja19_original_smallband_negative_finsum_card_le_total_count
      X hFinite T
  filter_upwards [hraw] with ω hω
  intro k t ht
  obtain ⟨F, hF, hsum⟩ := hω k t ht
  obtain ⟨F', hF', hsource⟩ :=
    avram_ja18j_public_original_compensated_finsum
      X k t ω
  have hFF : F' = F := Finset.ext (fun u => (hF' u).trans (hF u).symm)
  subst F'
  have hcomp :=
    avram_ja19_original_smallband_deterministic_compensator_mass_bound
      X hFinite T k t ht
  calc
    ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ =
        |(∑ u ∈ F, (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) -
          (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
            (-(1 / ((k : ℝ) + 1))), z ∂X.ν)| := by
      rw [hsource, Real.norm_eq_abs]
    _ ≤ |∑ u ∈ F, (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)| +
        |(t : ℝ) * (∫ z in Ioc (-1 : ℝ)
          (-(1 / ((k : ℝ) + 1))), z ∂X.ν)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le
          (∑ u ∈ F, (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          (0 : ℝ)
          ((t : ℝ) * (∫ z in Ioc (-1 : ℝ)
            (-(1 / ((k : ℝ) + 1))), z ∂X.ν)))
    _ ≤ (N ω).toReal + (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal :=
      add_le_add hsum hcomp
