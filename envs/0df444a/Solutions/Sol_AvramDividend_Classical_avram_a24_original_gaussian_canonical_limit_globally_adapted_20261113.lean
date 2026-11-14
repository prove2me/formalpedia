-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_gaussian_canonical_limit_globally_adapted_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:04:28.770248+00:00
-- url     : https://prove2.me/submissions/fd357299-3a59-4925-ba25-c06fc5d354eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original Gaussian intrinsic residual has a globally adapted canonical default-valued limit representative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) := by
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    Filter.limUnder atTop (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
  have hAdapt (t : ℝ≥0) : Measurable[𝓕 t] (G t) := by
    letI : MeasurableSpace Ω := 𝓕 t
    have hCut (n : ℕ) : StronglyMeasurable
        (fun ω : Ω => @avram_p4_h_gaussian_intrinsic_truncated_residual
          Ω mΩ P 𝓕 X n t ω) :=
      (@avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
        Ω mΩ P 𝓕 X n t).stronglyMeasurable
    have hStrong : StronglyMeasurable (G t) := by
      exact MeasureTheory.StronglyMeasurable.limUnder
        (l := atTop)
        (f := fun n : ℕ => fun ω : Ω =>
          @avram_p4_h_gaussian_intrinsic_truncated_residual Ω mΩ P 𝓕 X n t ω)
        hCut
    exact hStrong.measurable
  refine ⟨G, hAdapt, ?_⟩
  filter_upwards [hR] with ω hω
  intro t
  exact (hω t).limUnder_eq
