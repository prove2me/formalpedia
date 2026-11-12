-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja18i_original_zero_cutoff_gaussian_square_integrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:03:49.675427+00:00
-- url     : https://prove2.me/submissions/2a977e52-f244-4c6c-b91f-aea224efcce6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_zero_jump_gaussian_split
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (t : ℝ≥0), Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P := by
  intro t
  obtain ⟨Y, J, hν, hσ, hJ, heq⟩ :=
    avram_ja19_original_finite_activity_zero_jump_gaussian_split X hX hFinite t
  letI : IsProbabilityMeasure P := Y.isProbability
  have hq := (avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
    Y hν 0 t (by positivity)).1
  have hq' : Integrable (fun ω : Ω =>
      (Y.X t ω - (t : ℝ) * Y.c) ^ 2 - (t : ℝ) * Y.σ ^ 2) P := by
    simpa [Y.X_zero] using hq
  have hYsq : Integrable (fun ω : Ω =>
      (Y.X t ω - (t : ℝ) * Y.c) ^ 2) P := by
    have h := hq'.add (integrable_const ((t : ℝ) * Y.σ ^ 2))
    have heq :
        (fun ω : Ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2 - (t : ℝ) * Y.σ ^ 2) +
        (fun _ : Ω => (t : ℝ) * Y.σ ^ 2) =
        (fun ω : Ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2) := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [heq] at h
    exact h
  have hmeas : Measurable (fun ω : Ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) :=
    (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted X 0 t).mono
      (𝓕.le t) le_rfl
  have hbound : Integrable (fun ω : Ω =>
      2 * (Y.X t ω - (t : ℝ) * Y.c) ^ 2 + 2 * (J ω) ^ 2) P :=
    (hYsq.const_mul 2).add (hJ.const_mul 2)
  refine hbound.mono' (hmeas.aestronglyMeasurable.pow 2) ?_
  filter_upwards [heq] with ω hω
  rw [hω]
  have hb : ((Y.X t ω - (t : ℝ) * Y.c) + J ω) ^ 2 ≤
      2 * (Y.X t ω - (t : ℝ) * Y.c) ^ 2 + 2 * (J ω) ^ 2 := by
    nlinarith [sq_nonneg ((Y.X t ω - (t : ℝ) * Y.c) - J ω)]
  have hl : 0 ≤ ((Y.X t ω - (t : ℝ) * Y.c) + J ω) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hl]
  exact hb
