-- Prove2me | solution 1 for AvramDividend.Classical.chat04_terminal_restricted_actual_grid_reversal_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:21:32.939974+00:00
-- url     : https://prove2.me/submissions/b6f456a2-ffba-4123-89b9-1fe56d41f6d3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_increment_vector_tilted_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_vector_strict_drawdown_minimum_of_reversal_law
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_reverse_preserves_sum

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (a c : ℝ) :
    (let ν : Measure (Fin n → ℝ) :=
       ((Measure.map (fun ω : Ω => fun i : Fin n =>
         X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
         (fun v : Fin n → ℝ =>
           if (∑ i : Fin n, v i) < c then (1 : ℝ≥0∞) else 0))
     let w : (Fin n → ℝ) → ℕ → ℝ :=
       fun v j => if hj : j < n then v ⟨j, hj⟩ else 0
     ν {v : Fin n → ℝ | ∃ k : Fin n.succ,
       Finset.sum (Finset.range n) (w v) -
         Finset.sum (Finset.range k.val) (w v) < a} =
     ν {v : Fin n → ℝ | ∃ k : Fin n.succ,
       Finset.sum (Finset.range k.val) (w v) < a}) := by
  intro ν w
  have hwm : Measurable (fun v : Fin n → ℝ =>
      if (∑ i : Fin n, v i) < c then (1 : ℝ≥0∞) else 0) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
      measurable_const
  have hwR : ∀ v : Fin n → ℝ,
      (fun v : Fin n → ℝ => if (∑ i : Fin n, v i) < c then (1 : ℝ≥0∞) else 0)
        (fun i => v i.rev) =
      (fun v : Fin n → ℝ => if (∑ i : Fin n, v i) < c then (1 : ℝ≥0∞) else 0) v := by
    intro v
    simp only [AvramDividend.Classical.avram_ws01e_b_fin_reverse_preserves_sum n v]
  have hrevm : Measurable (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hrev : Measure.map (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) ν = ν := by
    ext A hA
    rw [Measure.map_apply hrevm hA]
    exact AvramDividend.Classical.avram_ws01e_b_levy_increment_vector_tilted_reversal
      X δ n _ hwm hwR A hA
  exact AvramDividend.Classical.avram_ws01e_b_fin_vector_strict_drawdown_minimum_of_reversal_law
    n ν a hrev
