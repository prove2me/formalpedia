-- Prove2me | solution 1 for ChinesePostman.Polyhedron.w_nonneg_automatic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T21:44:47.271454+00:00
-- url     : https://prove2.me/submissions/0ad02853-f6d3-4eff-9cb2-d4a990cded42

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

/-- From (3.3) with `x ≥ 0`: `2 w_n = incidentSum − b_n` is even and at least `-1`, hence `w_n ≥ 0`. -/
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ChinesePostman.Polyhedron.Graph V E) (x : E → ℤ) (w : V → ℤ)
    (hx : ∀ e, 0 ≤ x e)
    (h33 : ∀ n, ChinesePostman.Polyhedron.incidentSum G x n - 2 * w n =
      ChinesePostman.Polyhedron.bParity G n) :
    ∀ n, 0 ≤ w n := by
  intro n
  have hsum : 0 ≤ ChinesePostman.Polyhedron.incidentSum G x n := by
    unfold ChinesePostman.Polyhedron.incidentSum
    exact Finset.sum_nonneg fun e _ => hx e
  have hb0 : (0 : ℤ) ≤ ChinesePostman.Polyhedron.bParity G n := by
    unfold ChinesePostman.Polyhedron.bParity
    split_ifs <;> norm_num
  have hb1 : ChinesePostman.Polyhedron.bParity G n ≤ (1 : ℤ) := by
    unfold ChinesePostman.Polyhedron.bParity
    split_ifs <;> norm_num
  have hEq := h33 n
  omega

