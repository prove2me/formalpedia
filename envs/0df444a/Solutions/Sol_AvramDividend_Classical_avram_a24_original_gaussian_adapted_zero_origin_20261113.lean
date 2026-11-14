-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_gaussian_adapted_zero_origin_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:56:04.517334+00:00
-- url     : https://prove2.me/submissions/d4864878-f899-4e33-8028-694ed846d18b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_canonical_limit_globally_adapted_20261113
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original Gaussian source has a globally raw-filtration adapted representative starting exactly at zero. -/
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
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) := by
  obtain ⟨G, hAdapt, hEq⟩ :=
    avram_a24_original_gaussian_canonical_limit_globally_adapted_20261113
      X R hR
  have hZero :=
    avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
      X R hR
  let G' : ℝ≥0 → Ω → ℝ := fun t ω =>
    if t = 0 then 0 else G t ω
  have hAdapt' (t : ℝ≥0) : Measurable[𝓕 t] (G' t) := by
    by_cases ht : t = 0
    · simp [G', ht]
    · simpa [G', ht] using hAdapt t
  refine ⟨G', hAdapt', ?_, ?_⟩
  · intro ω
    simp [G']
  · filter_upwards [hEq, hZero] with ω hω h0
    intro t
    by_cases ht : t = 0
    · subst t
      simpa [G', h0]
    · simpa [G', ht] using hω t
