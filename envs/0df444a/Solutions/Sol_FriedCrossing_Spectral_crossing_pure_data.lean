-- Prove2me | solution 1 for FriedCrossing.Spectral.crossing_pure_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:03:50.914867+00:00
-- url     : https://prove2.me/submissions/82c9e17b-1c9d-4c43-9d69-e70ec44105cf

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Spectral_eval_Qpoly
import Theorems.Thm_FriedCrossing_Spectral_Qpoly_ne_zero
import Theorems.Thm_FriedCrossing_Spectral_charpoly_factor_locked
import Theorems.Thm_FriedCrossing_Spectral_rootMultiplicity_zero_locked

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    {scl snc : ℝ} (hne : scl ≠ snc) (hsnc : snc = 0) (hs : scl + snc = M.trace)
    (hp : scl * snc = M.det) (hlocked : ∀ z, M.charpoly.eval z = 0 → A.charpoly.eval z = 0)
    (hmult : A.charpoly.rootMultiplicity 0 = 2) : E₂ A M = 0 ∧ E₁ A M ≠ 0 := by
  have hscl : scl ≠ 0 := fun h => hne (h.trans hsnc.symm)
  have hfac := charpoly_factor_locked hne hs hp hlocked
  rw [hfac, hsnc, rootMultiplicity_zero_locked hscl] at hmult
  have hQ1 : (Qpoly (E₁ A M) (E₂ A M)).rootMultiplicity 0 = 1 := by omega
  have hroot : (Qpoly (E₁ A M) (E₂ A M)).IsRoot 0 :=
    (rootMultiplicity_pos (Qpoly_ne_zero _ _)).mp (by omega)
  have hE₂ : E₂ A M = 0 := by
    have := IsRoot.def.mp hroot
    rw [eval_Qpoly] at this
    simpa using this
  refine ⟨hE₂, fun hE₁ => ?_⟩
  have hQX : Qpoly (E₁ A M) (E₂ A M) = (X - C (0 : ℝ)) ^ 2 := by
    rw [hE₁, hE₂]; simp [Qpoly]
  rw [hQX, rootMultiplicity_X_sub_C_pow] at hQ1
  omega
end FriedCrossing.Spectral
