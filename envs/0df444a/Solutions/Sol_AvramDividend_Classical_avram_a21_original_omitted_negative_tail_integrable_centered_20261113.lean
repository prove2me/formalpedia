-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_omitted_negative_tail_integrable_centered_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:23:12.333191+00:00
-- url     : https://prove2.me/submissions/318dd6cb-8eae-4295-b92d-f220c8d15c9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_every_cutoff_residual_integrable_centered_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physically omitted compensated negative tail is integrable and centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) P ∧
      (∫ ω, avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω ∂P) = 0 := by
  intro n t
  have hCut :=
    avram_a21_original_every_cutoff_residual_integrable_centered_20261113
      X hX hFinite n t
  have hGauss :=
    avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
      X hX hFinite R hR t
  have hJint : Integrable (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) P :=
    hCut.1.sub hGauss.1
  have hJmean : (∫ ω,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω ∂P) = 0 := by
    rw [integral_sub hCut.1 hGauss.1, hCut.2, hGauss.2, sub_self]
  exact ⟨hJint, hJmean⟩
