-- Prove2me | solution 1 for FriedCrossing.Spectral.rootMultiplicity_zero_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:02:34.212514+00:00
-- url     : https://prove2.me/submissions/5273b77a-51e2-447c-b2f4-8e481c24493f

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Spectral_charpoly_fin_two_factor

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution {M : Matrix (Fin 2) (Fin 2) ℝ} {scl snc : ℝ}
    (hne : scl ≠ snc) (hsnc : snc = 0) (hs : scl + snc = M.trace) (hp : scl * snc = M.det) :
    M.charpoly.rootMultiplicity 0 = 1 := by
  have hscl : (0 : ℝ) ≠ scl := fun h => hne (h.symm.trans hsnc.symm)
  rw [charpoly_fin_two_factor hs hp, hsnc,
    rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]
  simp [hscl]
end FriedCrossing.Spectral
