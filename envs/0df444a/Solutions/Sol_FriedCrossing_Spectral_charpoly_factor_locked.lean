-- Prove2me | solution 1 for FriedCrossing.Spectral.charpoly_factor_locked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:02:42.978071+00:00
-- url     : https://prove2.me/submissions/56220c28-bbed-4a66-a1c7-6a5174ec165b

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_ClusterMatrix_eval_charpoly_eq_quartic
import Theorems.Thm_FriedCrossing_ClusterMatrix_eval_charpoly_fin_two
import Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_E__eq_51da910e0ce6
import Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_E__eq_1169bea58b61
import Theorems.Thm_FriedCrossing_PureZeros_quartic_factor


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    {scl snc : ℝ} (hne : scl ≠ snc) (hs : scl + snc = M.trace) (hp : scl * snc = M.det)
    (hlocked : ∀ z, M.charpoly.eval z = 0 → A.charpoly.eval z = 0) :
    A.charpoly = (X - C scl) * (X - C snc) * Qpoly (E₁ A M) (E₂ A M) := by
  have hroot : ∀ w, w = scl ∨ w = snc → M.charpoly.eval w = 0 := by
    rintro w (rfl | rfl) <;> rw [eval_charpoly_fin_two, ← hs, ← hp] <;> ring
  have h1 : PureZeros.quartic (c₁ A) (c₂ A) (c₃ A) (c₄ A) scl = 0 := by
    rw [← eval_charpoly_eq_quartic]; exact hlocked _ (hroot _ (Or.inl rfl))
  have h2 : PureZeros.quartic (c₁ A) (c₂ A) (c₃ A) (c₄ A) snc = 0 := by
    rw [← eval_charpoly_eq_quartic]; exact hlocked _ (hroot _ (Or.inr rfl))
  apply Polynomial.funext
  intro z
  rw [eval_charpoly_eq_quartic, PureZeros.quartic_factor hne h1 h2]
  simp only [Qpoly, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C]
  rw [E₁_eq A M hs, E₂_eq A M hs hp]
end FriedCrossing.Spectral
