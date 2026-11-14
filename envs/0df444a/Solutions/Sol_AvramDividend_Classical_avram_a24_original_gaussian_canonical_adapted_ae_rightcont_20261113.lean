-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_gaussian_canonical_adapted_ae_rightcont_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:03:49.438939+00:00
-- url     : https://prove2.me/submissions/d54fbe23-4c83-47a9-a32e-0c06cec2ad0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One globally adapted original Gaussian source representative starts at zero and is right-continuous on a common conull event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hRate : ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
        |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
          R T ω| ≤ ε) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) := by
  obtain ⟨G, hAdapt, hZero, hEq⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113 X R hR
  have hRight :=
    avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
      X R hRate
  refine ⟨G, hAdapt, hZero, ?_, hEq⟩
  filter_upwards [hEq, hRight] with ω hω hRC
  intro t
  have hFun : (fun u : ℝ≥0 => G u ω) =
      (fun u : ℝ≥0 => R u ω) := by
    funext u
    exact hω u
  rw [hFun]
  exact hRC t
