-- Prove2me | solution 1 for GenCostSched.GFCS.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:28:06.716246+00:00
-- url     : https://prove2.me/submissions/1bd7d3e0-ddd9-4f7f-b9e0-84fdb8b474e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model
import Theorems.Thm_GenCostSched_GFCS_speed_tradeoff

open MeasureTheory Set
open scoped ENNReal

open GenCostSched.GFCS in
theorem solution {n : ℕ} (I : Instance n) (H : Set (ℝ → ℝ)) (K : ℝ) (hI : I.Standing)
    (h2 : I.TwiceDiff) (hH : ∀ j, I.g j ∈ H) (hMS : IsMonotoneSubstitute H)
    (hK : I.CurvBound K) (X : ℕ → Fin n → ℝ → ℝ) (hX : I.IsAlg2Run X) :
    I.algCost X ≤ 2 * I.optLP (1 / (2 * K)) := by
  have hK1 : 1 ≤ K := hK.1
  have h := speed_tradeoff I H K hI h2 hH hMS hK X hX (2 * K - 1) (by linarith)
  have e1 : (1 : ℝ) + (2 * K - 1) = 2 * K := by ring
  have e2 : (2 * K) / (2 * K - K) = 2 := by
    rw [show 2 * K - K = K by ring]; field_simp
  rw [e1, e2] at h
  simpa using h
