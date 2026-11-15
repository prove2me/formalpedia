-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_gaussian_compact_pathwise_uniform_bound_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:47:35.237208+00:00
-- url     : https://prove2.me/submissions/48ec2177-8cc2-4f35-902c-33dda67bb80d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ≥0, t ≤ T → ‖R t ω‖ ≤ K := by
  have hCont :=
    AvramDividend.Classical.avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
      X hFinite R hR
  filter_upwards [hCont] with ω hCω
  have hImage : IsCompact ((fun t : ℝ≥0 => R t ω) '' Icc (0 : ℝ≥0) T) :=
    isCompact_Icc.image_of_continuousOn hCω.continuousOn
  obtain ⟨K, hK⟩ := hImage.isBounded.exists_norm_le
  refine ⟨max K 0, le_max_right K 0, ?_⟩
  intro t ht
  have hmem : t ∈ Icc (0 : ℝ≥0) T :=
    ⟨by positivity, ht⟩
  calc
    ‖R t ω‖ ≤ K := hK _ (mem_image_of_mem _ hmem)
    _ ≤ max K 0 := le_max_left K 0
