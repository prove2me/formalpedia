-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_sameX_intrinsic_gaussian_and_smallmark_limits_simultaneously_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:51:07.532397+00:00
-- url     : https://prove2.me/submissions/a1f8611c-bf1a-40a5-af7e-da533df64c5f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every choice of the original intrinsic Gaussian and smallmark pathwise limits agrees a.e. simultaneously in time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R S J K : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (nhds (R t ω)))
    (hS : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (nhds (S t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (nhds (J t ω)))
    (hK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (nhds (K t ω))) :
    ∀ᵐ ω ∂P, (∀ t : ℝ≥0, R t ω = S t ω) ∧
               (∀ t : ℝ≥0, J t ω = K t ω) := by
  filter_upwards [hR, hS, hJ, hK] with ω hωR hωS hωJ hωK
  constructor
  · intro t
    exact tendsto_nhds_unique (hωR t) (hωS t)
  · intro t
    exact tendsto_nhds_unique (hωJ t) (hωK t)
