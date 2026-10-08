-- Prove2me | solution 1 for DantzigSelector.Sparse.tube_constraint
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T00:54:12.810978+00:00
-- url     : https://prove2.me/submissions/b7dad7b6-c6c3-421b-a099-73ed3cf97cc1

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model

open CandesTao.Decoding DantzigSelector.Sparse in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (β b : Fin p → ℝ)
    (hX : UnitNormColumns X) (z : Fin n → ℝ) (lam : ℝ)
    (hz : ∀ j : Fin p, |∑ i, X i j * z i| ≤ lam)
    (hb : DantzigFeasible X (X.mulVec β + z) lam b) :
    ∀ j : Fin p, |∑ i, X i j * X.mulVec (b - β) i| ≤ 2 * lam := by
  intro j
  have h1 := hz j
  have h2 := hb j
  have key : ∑ i, X i j * X.mulVec (b - β) i
      = ∑ i, X i j * z i - ∑ i, X i j * ((X.mulVec β + z) i - X.mulVec b i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [key]
  calc |∑ i, X i j * z i - ∑ i, X i j * ((X.mulVec β + z) i - X.mulVec b i)|
      ≤ |∑ i, X i j * z i| + |∑ i, X i j * ((X.mulVec β + z) i - X.mulVec b i)| := abs_sub _ _
    _ ≤ lam + lam := add_le_add h1 h2
    _ = 2 * lam := by ring
