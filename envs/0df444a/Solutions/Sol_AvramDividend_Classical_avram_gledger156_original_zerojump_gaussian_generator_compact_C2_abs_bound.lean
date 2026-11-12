-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger156_original_zerojump_gaussian_generator_compact_C2_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:57:02.608207+00:00
-- url     : https://prove2.me/submissions/e062cb61-4303-4fc7-bf58-54027e595244

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (y M : ℝ)
    (hM : 0 ≤ M) (hw : |w y| ≤ M)
    (hd : |deriv w y| ≤ M)
    (hdd : |iteratedDeriv 2 w y| ≤ M) :
    |X.generator w y - q * w y| ≤
      (X.σ ^ 2 / 2 + |X.c| + q) * M := by
  rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hNuZero w y]
  have hs : 0 ≤ X.σ ^ 2 / 2 := by positivity
  have hc : 0 ≤ |X.c| := abs_nonneg _
  calc
    |X.σ ^ 2 / 2 * iteratedDeriv 2 w y + X.c * deriv w y - q * w y| ≤
        |X.σ ^ 2 / 2 * iteratedDeriv 2 w y| +
          (|X.c * deriv w y| + |q * w y|) := by
      calc
        _ = |X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
            (X.c * deriv w y - q * w y)| := by congr 1 <;> ring
        _ ≤ |X.σ ^ 2 / 2 * iteratedDeriv 2 w y| +
            |X.c * deriv w y - q * w y| := abs_add_le _ _
        _ ≤ |X.σ ^ 2 / 2 * iteratedDeriv 2 w y| +
            (|X.c * deriv w y| + |q * w y|) := by
          gcongr
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (X.c * deriv w y) (0 : ℝ) (q * w y))
    _ = (X.σ ^ 2 / 2) * |iteratedDeriv 2 w y| +
          (|X.c| * |deriv w y| + q * |w y|) := by
      simp only [abs_mul, abs_of_nonneg hs, abs_of_nonneg hq]
    _ ≤ (X.σ ^ 2 / 2) * M + (|X.c| * M + q * M) := by
      gcongr
    _ = (X.σ ^ 2 / 2 + |X.c| + q) * M := by ring
