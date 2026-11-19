-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_intrinsic_R_gaussian_variance_and_fulljump_cross_of_constructed_martingale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:31:00.343452+00:00
-- url     : https://prove2.me/submissions/780a05a9-826e-41d7-89db-e25ce1adc941
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_jump_cross_zero_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Extract the precise Gaussian-square and full negative-mark orthogonality lemmas. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P)
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) :
    (∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      let cross : Ω → ℝ := fun ω =>
        (R t ω - R s ω) *
          ((X.X t ω - X.X s ω) - (R t ω - R s ω))
      Integrable cross P ∧ (∫ ω, cross ω ∂P) = 0) := by

  refine ⟨?_, ?_⟩
  · exact avram_ja22_original_limit_gaussian_exact_square_moment
      X hX hFinite R hRsource
  · exact avram_mix_fin16_gaussian_residual_original_jump_cross_zero_public
      X hX hFinite R hRsource hRadapt
