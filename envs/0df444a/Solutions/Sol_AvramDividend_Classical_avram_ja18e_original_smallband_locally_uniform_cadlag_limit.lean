-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18e_original_smallband_locally_uniform_cadlag_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:56:02.727562+00:00
-- url     : https://prove2.me/submissions/766149ff-c266-499e-abb9-f6e9c8179193

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
import Theorems.Thm_AvramDividend_Classical_avram_ja18c_original_smallband_uniform_cutoff_difference_rate
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_smallband_cutoff_rightcont_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_uniform_cutoff_rate_rightcont_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original compensated physical small-band paths have a locally
uniform right-continuous limit on the original sample space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Ici t) t) ∧
      (∀ᵐ ω ∂P, Jsmall 0 ω = 0) := by
  classical
  let Good (ω : Ω) : Prop :=
    ∀ T : ℝ≥0,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤
  have hGood : ∀ᵐ ω ∂P, Good ω :=
    avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
      X hFinite
  have hAnal (ω : Ω) (hω : Good ω) :
      ∃ g : ℝ≥0 → ℝ,
        (∀ t : ℝ≥0, Tendsto (fun n : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
          atTop (𝓝 (g t))) ∧
        (∀ t : ℝ≥0, ContinuousWithinAt g (Ici t) t) ∧
        g 0 = 0 := by
    apply avram_ja18h_uniform_cutoff_rate_rightcont_limit
    · intro n t
      exact (avram_ja18g_original_smallband_cutoff_rightcont_zero X n ω).1 t
    · intro n
      exact (avram_ja18g_original_smallband_cutoff_rightcont_zero X n ω).2
    · intro T
      let N := ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
      let C : ℝ := N.toReal + ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
      refine ⟨C, add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ?_⟩
      intro n m hnm t htt
      simpa only [C, N] using
        (avram_ja18c_original_smallband_uniform_cutoff_difference_rate
          X hFinite T ω (hω T) n m hnm t htt)
  let Jsmall (t : ℝ≥0) (ω : Ω) : ℝ :=
    if hω : Good ω then Classical.choose (hAnal ω hω) t else 0
  refine ⟨Jsmall, ?_, ?_, ?_⟩
  · filter_upwards [hGood] with ω hω
    intro t
    simpa only [Jsmall, dif_pos hω] using
      (Classical.choose_spec (hAnal ω hω)).1 t
  · filter_upwards [hGood] with ω hω
    intro t
    simpa only [Jsmall, dif_pos hω] using
      (Classical.choose_spec (hAnal ω hω)).2.1 t
  · filter_upwards [hGood] with ω hω
    simpa only [Jsmall, dif_pos hω] using
      (Classical.choose_spec (hAnal ω hω)).2.2
