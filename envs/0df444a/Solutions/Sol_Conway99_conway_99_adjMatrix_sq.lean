-- Prove2me | solution 1 for Conway99.conway_99_adjMatrix_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T16:52:15.538498+00:00
-- url     : https://prove2.me/submissions/07dde4c4-455b-4235-9d17-c0db1557a4c9

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Matrix.Basic

open SimpleGraph

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    (g.adjMatrix ℤ) ^ 2 + g.adjMatrix ℤ =
      12 • (1 : Matrix V V ℤ) + 2 • (Matrix.of fun _ _ => (1 : ℤ)) := by
  classical
  have hm : (g.adjMatrix ℤ) ^ 2
      = (14 : ℕ) • (1 : Matrix V V ℤ) + (1 : ℕ) • g.adjMatrix ℤ
        + (2 : ℕ) • (gᶜ).adjMatrix ℤ := h.matrix_eq
  have hc : (gᶜ).adjMatrix ℤ
      = (Matrix.of fun _ _ => (1 : ℤ)) - 1 - g.adjMatrix ℤ := by
    ext v w
    by_cases hvw : v = w
    · subst hvw
      simp [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, Matrix.one_apply]
    · by_cases ha : g.Adj v w <;>
        simp [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, Matrix.one_apply_ne hvw,
          hvw, ha]
  rw [hm, hc]
  ext v w
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one]
  ring
