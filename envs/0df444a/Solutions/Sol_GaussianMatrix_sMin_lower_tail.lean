-- Prove2me | solution 1 for GaussianMatrix.sMin_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:33:07.54837+00:00
-- url     : https://prove2.me/submissions/affaca45-d872-48ee-ba90-7fe74386c951

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_gordon
import Theorems.Thm_GaussianMatrix_gaussian_concentration
import Theorems.Thm_GaussianMatrix_sMin_lipschitz

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (u : ℝ) (hu : 0 ≤ u) :
    (gaussianMatrix N n) {A | sMin (Matrix.of A) ≤ Real.sqrt N - Real.sqrt n - u}
      ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) := by
  set h : (Fin N → Fin n → ℝ) → ℝ := fun X => -sMin (Matrix.of X) with hh
  have hLip : ∀ X Y, |h X - h Y| ≤ 1 * frobNorm (Matrix.of X - Matrix.of Y) := by
    intro X Y
    have := sMin_lipschitz (Matrix.of X) (Matrix.of Y)
    simp only [hh, one_mul]
    rw [show -sMin (Matrix.of X) - -sMin (Matrix.of Y)
        = -(sMin (Matrix.of X) - sMin (Matrix.of Y)) by ring, abs_neg]
    exact this
  obtain ⟨-, hconc⟩ := gaussian_concentration h 1 one_pos hLip u hu
  obtain ⟨-, -, hmean, -, -⟩ := gordon (N := N) hn
  have hint : ∫ Y, h Y ∂(gaussianMatrix N n) = -∫ Y, sMin (Matrix.of Y) ∂(gaussianMatrix N n) := by
    simp only [hh]
    exact integral_neg _
  refine le_trans (measure_mono ?_) hconc
  intro X hX
  simp only [Set.mem_ofPred_eq] at hX ⊢
  rw [hint]
  simp only [hh]
  linarith
