-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:16:07.878845+00:00
-- url     : https://prove2.me/submissions/20b833eb-f91b-4974-8406-beafc6ddd494

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true Gaussian source is uniformly bounded on the interior mask. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |G p| ≤ C := by
  dsimp
  obtain ⟨M, hM0, hM⟩ :=
    derivative_abs_le_on_compact_interior_interval
      w a b u v hw hau huv hvb
  refine ⟨|X.σ| * M, mul_nonneg (abs_nonneg _) hM0, ?_⟩
  intro p
  by_cases hp : (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∈ Icc u v
  · simp only [if_pos hp, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _ hp.1 hp.2) (abs_nonneg _)
  · simp only [if_neg hp, mul_zero, abs_zero]
    exact mul_nonneg (abs_nonneg _) hM0
