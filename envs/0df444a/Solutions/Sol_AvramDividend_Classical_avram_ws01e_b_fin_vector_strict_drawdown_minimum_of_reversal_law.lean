-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_fin_vector_strict_drawdown_minimum_of_reversal_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T09:30:12.203493+00:00
-- url     : https://prove2.me/submissions/53a4c687-4557-4697-826e-b7c6d5cf6e25

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_general_strict_prefix_reversal_of_law

theorem solution
    (n : ℕ) (μ : MeasureTheory.Measure (Fin n → ℝ)) (a : ℝ)
    (hrev : MeasureTheory.Measure.map
      (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) μ = μ) :
    let w : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => if hj : j < n then v ⟨j, hj⟩ else 0
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) (w v) -
        Finset.sum (Finset.range k.val) (w v) < a} =
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) (w v) < a} := by
  intro w
  refine AvramDividend.Classical.avram_ws01e_b_general_strict_prefix_reversal_of_law n μ a w hrev ?_
  intro v k hk
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
  have h2 : n - 1 - j < n := by omega
  simp only [w, dif_pos hj', dif_pos h2]
  congr 1
  ext; simp [Fin.rev]; omega
