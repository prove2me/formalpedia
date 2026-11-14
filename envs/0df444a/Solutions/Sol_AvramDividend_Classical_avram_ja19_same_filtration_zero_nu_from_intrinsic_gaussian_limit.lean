-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_same_filtration_zero_nu_from_intrinsic_gaussian_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:47:40.305211+00:00
-- url     : https://prove2.me/submissions/a982b7e9-ac23-4536-9728-8e53ee3f44f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja19_canonical_zero_nu_companion_original_filtered_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Source limit uniqueness transfers a single original-space Gaussian companion to any prescribed limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by
  obtain ⟨Y, hNu, hSigma, hYLimit⟩ :=
    avram_ja19_canonical_zero_nu_companion_original_filtered_source
      X hX hFinite
  refine ⟨Y, hNu, hSigma, ?_⟩
  filter_upwards [hR, hYLimit] with ω hRω hYω
  intro t
  exact tendsto_nhds_unique (hRω t) (hYω t)
