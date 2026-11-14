-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_omitted_negative_tail_integrable_L1_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:21:14.816173+00:00
-- url     : https://prove2.me/submissions/a21e5906-7e09-4c5e-a16b-828be04ed2b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_omitted_nearzero_tail_exact_square_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical omitted compensated near-zero negative mark tail is source L1. -/
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
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) P := by
  intro n t
  letI : IsProbabilityMeasure P := X.isProbability
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
  have hCut (k : ℕ) (T : ℝ≥0) :
      Measurable[𝓕.rightCont T]
        (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω) :=
    (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X k T).mono (𝓕.le_rightCont T) le_rfl
  have hRmeas : AEStronglyMeasurable (R t) P :=
    (avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
      X hCut R hR t).mono ((𝓕.rightCont).le t)
  have hCutMeas : AEStronglyMeasurable
      (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hJmeas : AEStronglyMeasurable J P := hCutMeas.sub hRmeas
  have hJ2 :=
    avram_ja22_original_omitted_nearzero_tail_exact_square_moment
      X hX hFinite R hR n t
  change Integrable (fun ω => (J ω) ^ 2) P ∧ _ at hJ2
  have hLp : MemLp J 2 P :=
    (memLp_two_iff_integrable_sq hJmeas).2 hJ2.1
  exact hLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
