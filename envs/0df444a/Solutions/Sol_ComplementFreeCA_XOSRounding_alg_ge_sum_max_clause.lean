-- Prove2me | solution 1 for ComplementFreeCA.XOSRounding.alg_ge_sum_max_clause
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:57:30.510983+00:00
-- url     : https://prove2.me/submissions/f6c8e8cd-d9be-49a7-92f8-55d4b49cef3e

import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_XOSRounding_Model
import Definitions.Def_ComplementFreeCA_XOSRounding_Algorithm
open Finset ComplementFreeCA.XOSRounding

theorem solution {n m : ℕ} (hn : 0 < n)
    (W : Fin n → Finset (Fin m → ℝ)) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsXOSWith (v i) (W i))
    (cl : Fin n → Finset (Fin m) → Fin m → ℝ) (hcl : ∀ i, IsXOSOracle (v i) (W i) (cl i))
    (win : (Fin n → Finset (Fin m)) → Fin m → Fin n) (hwin : IsHighestClauseRule cl win)
    (σ : Fin n → Finset (Fin m)) :
    ∑ j, maxClauseEntry hn cl σ j ≤ algWelfare v win σ := by
  have hmax : ∀ j, maxClauseEntry hn cl σ j = cl (win σ j) (σ (win σ j)) j := by
    intro j
    apply le_antisymm
    · apply sup'_le
      intro i hi
      exact hwin σ j i
    · exact le_sup' (f := fun i => cl i (σ i) j) (mem_univ (win σ j))
  simp_rw [hmax]
  have he : (∑ j, cl (win σ j) (σ (win σ j)) j) =
      ∑ i, ∑ j ∈ algAllocation win σ i, cl i (σ i) j := by
    simp only [algAllocation, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    simp [eq_comm]
  rw [he]
  apply sum_le_sum
  intro i hi
  exact (hv i).2 _ |>.2 _ (hcl i (σ i)).1
