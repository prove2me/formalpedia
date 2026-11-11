-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_finite_mark_block_shift_identDistrib
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:51:43.2536+00:00
-- url     : https://prove2.me/submissions/bd694966-a203-4db0-84fe-45309fd1236d

import Mathlib.Probability.IdentDistrib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_mark_stream_shift_identDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A fixed-length sum of the original iid marks is invariant under index shifts. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (m n : ℕ) :
    IdentDistrib (fun ω => ∑ j ∈ Finset.range n, Y (m + j) ω)
      (fun ω => ∑ j ∈ Finset.range n, Y j ω) P P := by
  have hshift :=
    AvramDividend.Classical.avram_a06_original_cp_mark_stream_shift_identDistrib
      P τ Y hd m
  have hsum : Measurable (fun v : ℕ → ℝ => ∑ j ∈ Finset.range n, v j) :=
    Finset.measurable_sum (Finset.range n)
      (fun j hj => measurable_pi_apply j)
  change IdentDistrib
    ((fun v : ℕ → ℝ => ∑ j ∈ Finset.range n, v j) ∘
      (fun ω j => Y (m + j) ω))
    ((fun v : ℕ → ℝ => ∑ j ∈ Finset.range n, v j) ∘
      (fun ω j => Y j ω)) P P
  exact hshift.comp hsum
