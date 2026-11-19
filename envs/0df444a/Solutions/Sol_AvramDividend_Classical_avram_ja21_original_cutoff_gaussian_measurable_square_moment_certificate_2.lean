-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:28:36.469699+00:00
-- url     : https://prove2.me/submissions/b22756c2-2ebe-4607-bc0f-592fb9cadda3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_omitted_tail_zero_cross
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_omitted_nearzero_tail_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_cutoff_minus_intrinsic_gaussian_limit_ae_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Correct Gaussian core and omitted negative tail with exact same-X variance, rather than the false retained-band variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      ∃ (G J : Ω → ℝ),
        (∀ᵐ ω ∂P,
          avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω = G ω + J ω) ∧
        AEStronglyMeasurable G P ∧
        AEStronglyMeasurable J P ∧
        Integrable (fun ω => (G ω) ^ 2) P ∧
        Integrable (fun ω => (J ω) ^ 2) P ∧
        (∫ ω, G ω * J ω ∂P) = 0 ∧
        (∫ ω, (G ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 ∧
        (∫ ω, (J ω) ^ 2 ∂P) =
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  obtain ⟨R, hRsource, hRadapt, hRint, hRmart⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  have hRlim : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)) := by
    filter_upwards [hRsource] with ω hω
    exact hω.1
  intro n t
  let G : Ω → ℝ := R t
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
  have hGSq := avram_ja22_original_limit_gaussian_exact_square_moment
    X hX hFinite R hRlim t
  have hJSq := avram_ja22_original_omitted_nearzero_tail_exact_square_moment
    X hX hFinite R hRlim n t
  refine ⟨G, J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [] with ω
    dsimp [G, J]
    ring
  · exact (hRint t).aestronglyMeasurable
  · exact avram_ja18_original_cutoff_minus_intrinsic_gaussian_limit_ae_measurable
      X R (fun t => (hRint t).aestronglyMeasurable) n t
  · exact hGSq.1
  · exact hJSq.1
  · exact avram_ja22_original_limit_gaussian_omitted_tail_zero_cross
      X hX hFinite R hRlim n t
  · exact hGSq.2
  · exact hJSq.2
