-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.Law.expect_pi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:53.936648+00:00
-- url     : https://prove2.me/submissions/3554a104-609e-47e1-b09b-8f600569ed20

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointLaw

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
open ConsistentSubmodular.Checkpoints.Law
variable {Ω : Type*} [Fintype Ω]

theorem solution {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (μ : ι → Law X) (i : ι) (F : X → ℝ) :
    (pi μ).expect (fun x => F (x i)) = (μ i).expect F := by
  let g : ι → X → ℝ := fun j a => (μ j).weight a * if j = i then F a else 1
  have hpoint (x : ι → X) : (∏ j, (μ j).weight (x j)) * F (x i) = ∏ j, g j (x j) := by
    simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hrow (j : ι) : ∑ a, g j a = if j = i then (μ i).expect F else 1 := by
    by_cases hji : j = i
    · subst hji
      simp [g, expect]
    · simp [g, hji, (μ j).sum_one]
  calc (pi μ).expect (fun x => F (x i))
      = ∑ x : ι → X, ∏ j, g j (x j) := by
        simp only [expect, pi]
        exact Finset.sum_congr rfl fun x _ => hpoint x
    _ = ∏ j, ∑ a, g j a := (Fintype.prod_sum g).symm
    _ = (μ i).expect F := by
        simp only [hrow, Finset.prod_ite_eq', Finset.mem_univ, if_true]

end
