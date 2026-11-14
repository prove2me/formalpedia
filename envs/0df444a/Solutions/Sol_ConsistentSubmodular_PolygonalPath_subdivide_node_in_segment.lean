-- Prove2me | solution 1 for ConsistentSubmodular.PolygonalPath.subdivide_node_in_segment
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:35.835766+00:00
-- url     : https://prove2.me/submissions/526f56c6-17a2-478a-928b-686f33950cb8

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision

section

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}
open ConsistentSubmodular.PolygonalPath

theorem solution (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N)
    (a : Fin γ.pieces) (r : ℕ) (hr : r ≤ N) :
    (γ.subdivide N).node ⟨a.val * N + r, by
      dsimp only [subdivide_pieces]
      have := a.isLt
      nlinarith⟩ = mix (γ.node a.castSucc) (γ.node a.succ) ((r : ℝ) / N) := by
  by_cases hrN : r < N
  · have hdiv : (a.val * N + r) / N = a.val := by
      rw [Nat.mul_comm a.val N, Nat.mul_add_div hN, Nat.div_eq_of_lt hrN, Nat.add_zero]
    have hmod : (a.val * N + r) % N = r := by simp [Nat.add_mod, Nat.mod_eq_of_lt hrN]
    simp only [subdivide, hdiv, a.isLt, dite_true, hmod]
    rfl
  · have hrEq : r = N := by omega
    subst r
    have hdiv : (a.val * N + N) / N = a.val + 1 := by
      have he : a.val * N + N = (a.val + 1) * N := by ring
      rw [he, Nat.mul_div_cancel _ hN]
    have hmod : (a.val * N + N) % N = 0 := by simp
    have hnR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simp only [subdivide, hdiv, hmod, Nat.cast_zero, zero_div, mix_zero, div_self hnR,
      mix_one]
    split_ifs with ha
    · rfl
    · congr 1
      apply Fin.ext
      have := a.isLt
      simp only [Fin.val_last, Fin.val_succ]
      omega

end
