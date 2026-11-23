-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_finite_activity_global_intrinsic_martingale_fields
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:38:25.465167+00:00
-- url     : https://prove2.me/submissions/e9f6a9ef-a7b8-4427-80fe-9e29c017ed9d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b213_original_global_intrinsic_martingales_and_canonical_unmarked_grid_split
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)

 :
    ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) := by
  obtain ⟨R, Jsmall, M, hRsrc, hJsrc, hRI, hJI, hRM, hJM, hDecomp, _⟩ :=
    AvramDividend.Classical.avram_b213_original_global_intrinsic_martingales_and_canonical_unmarked_grid_split X hX hFinite
      (∅ : Finset ℕ) (fun _ _ => 0) (fun _ _ => 0)
      (by simp) (fun _ => ∅) (by simp)
  exact ⟨R, Jsmall, M, hRsrc, hJsrc, hRI, hJI, hRM, hJM, hDecomp⟩
