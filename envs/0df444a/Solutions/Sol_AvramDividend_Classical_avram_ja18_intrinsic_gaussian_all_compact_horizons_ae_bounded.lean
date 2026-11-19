-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_intrinsic_gaussian_all_compact_horizons_ae_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:20:03.283833+00:00
-- url     : https://prove2.me/submissions/828b858e-5add-4a20-ac87-bdee7503a35f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Continuous original Gaussian sample paths admit finite bounds on all compact horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ B : ℝ,
      ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) → ‖R t ω‖ ≤ B := by
  have hCont :
      ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => R t ω) :=
    avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
      X hFinite R hR
  filter_upwards [hCont] with ω hω
  intro n
  have hc : IsCompact (Set.Icc (0 : ℝ≥0) (n : ℝ≥0)) :=
    isCompact_Icc
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hω.continuousOn
  refine ⟨B, ?_⟩
  intro t ht
  exact hB t ⟨(by exact bot_le), ht⟩
