-- Prove2me | solution 2 for AvramDividend.Classical.avram_a28_original_intrinsic_gaussian_raw_allpath_cadlag_regularity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:30:51.125735+00:00
-- url     : https://prove2.me/submissions/ca0189cc-970b-42b3-bbf5-cb1457147212
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a29_sigma_zero_gaussian_intrinsic_raw_allpath_regularity_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a29_original_positive_sigma_intrinsic_gaussian_raw_allpath_cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ ω t, ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
        G t ω ≤ l) := by
  by_cases hZero : X.σ = 0
  · exact avram_a29_sigma_zero_gaussian_intrinsic_raw_allpath_regularity_20261114
      X hX hFinite hZero R hR
  · have hPositive : 0 < X.σ :=
      lt_of_le_of_ne X.σ_nonneg (Ne.symm hZero)
    exact avram_a29_original_positive_sigma_intrinsic_gaussian_raw_allpath_cadlag
      X hX hFinite hPositive R hR
