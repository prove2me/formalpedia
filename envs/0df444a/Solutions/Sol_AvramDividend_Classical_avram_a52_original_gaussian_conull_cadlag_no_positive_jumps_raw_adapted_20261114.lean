-- Prove2me | solution 1 for AvramDividend.Classical.avram_a52_original_gaussian_conull_cadlag_no_positive_jumps_raw_adapted_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:02:57.27776+00:00
-- url     : https://prove2.me/submissions/111efce9-a04b-4b8f-aa2f-b0085d0f5d7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a51_continuous_real_path_has_allpath_cadlag_no_positive_jumps_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian representative has the complete cadlag and no-upward-jump properties simultaneously on a single conull event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P,
        (∀ t, ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
        (∀ t, 0 < t → ∃ l,
          Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l)) ∧
        (∀ t l, 0 < t →
          Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
          G t ω ≤ l)) := by
  obtain ⟨G, hAdapt, hZero, hEq, hCont⟩ :=
    avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
      X hFinite R hR
  refine ⟨G, hAdapt, hZero, hEq, ?_⟩
  filter_upwards [hCont] with ω hω
  exact avram_a51_continuous_real_path_has_allpath_cadlag_no_positive_jumps_20261114
    (fun t => G t ω) hω
