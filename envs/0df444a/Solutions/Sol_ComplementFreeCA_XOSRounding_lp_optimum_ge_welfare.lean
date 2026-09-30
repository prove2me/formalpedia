-- Prove2me | solution 1 for ComplementFreeCA.XOSRounding.lp_optimum_ge_welfare
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:33:59.135344+00:00
-- url     : https://prove2.me/submissions/9f0295a8-90ac-47c3-b70a-9beeab1780a7

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSRounding_Model
open Finset ComplementFreeCA.XOSRounding

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPOptimal v x)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare v O ≤ lpValue v x := by
  classical
  let y : Fin n → Finset (Fin m) → ℝ := fun i S => if S = O i then 1 else 0
  have hy : IsLPFeasible y := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [y, sum_ite_eq', mem_filter, mem_univ, true_and]
      by_cases he : ∃ i, j ∈ O i
      · obtain ⟨i, hi⟩ := he
        have hother : ∀ i' ≠ i, j ∉ O i' := by
          intro i' hne hj
          exact disjoint_left.mp (hO hne) hj hi
        rw [sum_eq_single i]
        · simp [hi]
        · intro i' hi' hne
          simp [hother i' hne]
        · simp
      · simp only [not_exists] at he
        simp [he]
    · intro i
      simp [y]
    · intro i S
      simp only [y]
      split_ifs <;> norm_num
  have heq : lpValue v y = welfare v O := by
    simp [lpValue, welfare, y, ite_mul]
  rw [← heq]
  exact hx.2 y hy
