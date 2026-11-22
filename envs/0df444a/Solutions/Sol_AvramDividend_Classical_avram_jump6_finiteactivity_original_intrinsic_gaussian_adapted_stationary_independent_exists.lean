-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_finiteactivity_original_intrinsic_gaussian_adapted_stationary_independent_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T22:39:34.828191+00:00
-- url     : https://prove2.me/submissions/a61586cd-25f2-4696-aacd-d6dca79d0016

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a24_canonical_gaussian_raw_adapted_stationary_independent_aeRC_20261114
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Reconstruct the original finite-activity intrinsic Gaussian component as a
single adapted right-continuous stationary-independent-increment process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ (R G : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ k ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
          |avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω -
            R T ω| ≤ ε) ∧
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, ∀ t,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ s T : ℝ≥0, Indep
        (MeasurableSpace.comap
          (fun ω => G (s + T) ω - G s ω) inferInstance)
        (𝓕 s) P) ∧
      (∀ T, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
            Measure.map Z P) := by
  obtain ⟨R, hR⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
      X hFinite
  have hPoint : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) :=
    hR.mono (fun ω hω => hω.1)
  have hRate : ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ k ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
        |avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω -
          R T ω| ≤ ε :=
    hR.mono (fun ω hω => hω.2)
  obtain ⟨G, hAdapt, hZero, hEqual, hRC, hIndep, hStat⟩ :=
    avram_a24_canonical_gaussian_raw_adapted_stationary_independent_aeRC_20261114
      X hX hFinite R hPoint hRate
  exact ⟨R, G, hPoint, hRate, hAdapt, hZero, hEqual, hRC, hIndep, hStat⟩

