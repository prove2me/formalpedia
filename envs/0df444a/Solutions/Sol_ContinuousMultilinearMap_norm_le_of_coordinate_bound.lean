-- Prove2me | solution 1 for ContinuousMultilinearMap.norm_le_of_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:11:03.054929+00:00
-- url     : https://prove2.me/submissions/f76debf5-3cfc-4409-b8fa-43a07eb140a0

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
set_option autoImplicit false

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n k : ℕ}
    (T : (EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ a : Fin k → Fin n, ‖T (fun j => EuclideanSpace.single (a j) 1)‖ ≤ M) :
    ‖T‖ ≤ (n : ℝ)^k * M := by
  classical
  apply T.opNorm_le_bound (by positivity)
  intro v
  have hv (j : Fin k) : (∑ i : Fin n, (v j i) • EuclideanSpace.single i 1) = v j := by
    ext i
    simp [Pi.single_apply]
  calc
    ‖T v‖ = ‖∑ a : Fin k → Fin n,
        (∏ j, v j (a j)) • T (fun j => EuclideanSpace.single (a j) 1)‖ := by
      conv_lhs => rw [show v = (fun j => ∑ i : Fin n, (v j i) • EuclideanSpace.single i 1) from funext fun j => (hv j).symm]
      rw [T.map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact T.map_smul_univ _ _
    _ ≤ ∑ a : Fin k → Fin n,
        ‖(∏ j, v j (a j)) • T (fun j => EuclideanSpace.single (a j) 1)‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin k → Fin n, (∏ j, ‖v j‖) * M := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod]
      exact mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => PiLp.norm_apply_le (v j) (a j))) (hb a) (norm_nonneg _) (by positivity)
    _ = (n : ℝ)^k * M * ∏ j, ‖v j‖ := by
      simp [mul_comm, mul_left_comm, mul_assoc]
