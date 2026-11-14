-- Prove2me | solution 1 for ConsistentSubmodular.PolygonalPath.subdivide_edge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:00.551168+00:00
-- url     : https://prove2.me/submissions/6a9e5841-dcb1-4ccc-bfa2-0ba263e824e4

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision
import Theorems.Thm_ConsistentSubmodular_PolygonalPath_subdivide_node_in_segment

section

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}
open ConsistentSubmodular.PolygonalPath

theorem solution (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N)
    (j : Fin (γ.subdivide N).pieces) :
    ∃ (a : Fin γ.pieces) (r : ℕ), r < N ∧
      (γ.subdivide N).node j.castSucc =
        mix (γ.node a.castSucc) (γ.node a.succ) ((r : ℝ) / N) ∧
      (γ.subdivide N).node j.succ =
        mix (γ.node a.castSucc) (γ.node a.succ) (((r : ℝ) + 1) / N) := by
  have hj : j.val < γ.pieces * N := j.isLt
  have ha : j.val / N < γ.pieces := (Nat.div_lt_iff_lt_mul hN).mpr hj
  let a : Fin γ.pieces := ⟨j.val / N, ha⟩
  let r := j.val % N
  have hr : r < N := Nat.mod_lt _ hN
  have he : a.val * N + r = j.val := by
    dsimp [a, r]
    simpa [Nat.mul_comm] using Nat.div_add_mod j.val N
  refine ⟨a, r, hr, ?_, ?_⟩
  · have h := γ.subdivide_node_in_segment N hN a r (Nat.le_of_lt hr)
    have hidx : (⟨a.val * N + r, by have := a.isLt; dsimp only [subdivide_pieces]; nlinarith⟩ :
        Fin ((γ.subdivide N).pieces + 1)) = j.castSucc := Fin.ext he
    rwa [hidx] at h
  · have h := γ.subdivide_node_in_segment N hN a (r + 1) (by omega)
    have hidx : (⟨a.val * N + (r + 1), by have := a.isLt; dsimp only [subdivide_pieces]; nlinarith⟩ :
        Fin ((γ.subdivide N).pieces + 1)) = j.succ := by apply Fin.ext; simp only [Fin.val_succ]; omega
    rw [hidx, Nat.cast_add, Nat.cast_one] at h
    exact h

end
