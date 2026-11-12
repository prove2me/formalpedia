-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_count_vector_finite_marks_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:29:29.418835+00:00
-- url     : https://prove2.me/submissions/da36b75a-a62a-4e52-aead-782e7b242210

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_vector_mark_independent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Count-vector independence survives measurable finite sums of original marks. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (n : ℕ) (t : Fin n → ℝ≥0) (m ℓ : ℕ) :
    IndepFun
      (fun ω (i : Fin n) => LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (t i : ℝ))
      (fun ω => ∑ j ∈ Finset.range ℓ, Y (m + j) ω) P := by
  have hbase :=
    AvramDividend.Classical.avram_a06_original_cp_count_vector_mark_independent
      P τ Y hd n t
  have hsum :
      Measurable (fun v : ℕ → ℝ => ∑ j ∈ Finset.range ℓ, v (m + j)) :=
    Finset.measurable_sum (Finset.range ℓ)
      (fun j hj => measurable_pi_apply (m + j))
  change IndepFun
    ((fun v : Fin n → ℕ => v) ∘
      (fun ω (i : Fin n) => LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (t i : ℝ)))
    ((fun v : ℕ → ℝ => ∑ j ∈ Finset.range ℓ, v (m + j)) ∘
      (fun ω j => Y j ω)) P
  exact hbase.comp measurable_id hsum
