-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja20_original_cutoff_gaussian_uncorrelated_components
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:45:28.705921+00:00
-- url     : https://prove2.me/submissions/c979b3ba-df4e-468d-88ba-d2c3e6a75140
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integrable_product_of_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      ∃ (G J : Ω → ℝ),
        (∀ᵐ ω ∂P,
          avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω = G ω + J ω) ∧
        Integrable (fun ω => (G ω) ^ 2) P ∧
        Integrable (fun ω => (J ω) ^ 2) P ∧
        Integrable (fun ω => G ω * J ω) P ∧
        (∫ ω, G ω * J ω ∂P) = 0 ∧
        (∫ ω, (G ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 ∧
        (∫ ω, (J ω) ^ 2 ∂P) =
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  intro n t
  obtain ⟨G, J, hR, hGMeas, hJMeas, hGsq, hJsq,
      hOrth, hGmom, hJmom⟩ :=
    avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
      X hX hFinite n t
  refine ⟨G, J, hR, hGsq, hJsq, ?_, hOrth, hGmom, hJmom⟩
  exact avram_ja20_integrable_product_of_square_integrable
    P G J hGMeas hJMeas hGsq hJsq
