-- Prove2me | solution 1 for BoydADMM.Convergence.dual_step_monotone
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:29:34.315978+00:00
-- url     : https://prove2.me/submissions/1b663082-fcaf-432b-964e-454951416052

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Theorems.Thm_BoydADMM_Convergence_z_update_dual_feasible
open Filter
open scoped Topology
namespace BoydADMM.Convergence

private lemma transpose_inner {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (u : EuclideanSpace ℝ (Fin a)) (v : EuclideanSpace ℝ (Fin b)) :
    inner ℝ (Matrix.toEuclideanLin M.transpose u) v = inner ℝ u (Matrix.toEuclideanLin M v) := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- Proof of (A.1), p. 110: `(y^{k+1} − y^k)ᵀ(B(z^{k+1} − z^k)) ≤ 0` for every book index
`k ≥ 1` (here written with `k + 1` in place of the book's `k`, so that `z^k` is itself a
`z`-update). -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    inner ℝ (y (k + 2) - y (k + 1)) (P.Bmul (z (k + 2) - z (k + 1))) ≤ 0 := by
  have hnew := z_update_dual_feasible P hA1 hρ hrun (k+1) (z (k+1)) (hrun.z_mem k)
  have hold := z_update_dual_feasible P hA1 hρ hrun k (z (k+2)) (hrun.z_mem (k+1))
  change inner ℝ (-P.BTmul (y (k+2))) (z (k+1)-z (k+2)) ≤
    P.g (z (k+1))-P.g (z (k+2)) at hnew
  change inner ℝ (-P.BTmul (y (k+1))) (z (k+2)-z (k+1)) ≤
    P.g (z (k+2))-P.g (z (k+1)) at hold
  simp only [inner_neg_left, Problem.BTmul, transpose_inner, inner_sub_right] at hnew hold
  simp only [inner_sub_left, Problem.Bmul, map_sub, inner_sub_right]
  linarith


