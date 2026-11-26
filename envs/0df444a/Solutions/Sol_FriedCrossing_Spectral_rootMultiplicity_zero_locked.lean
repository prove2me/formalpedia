-- Prove2me | solution 1 for FriedCrossing.Spectral.rootMultiplicity_zero_locked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:01:48.632509+00:00
-- url     : https://prove2.me/submissions/32bc9e09-d46b-43a6-8515-04fd84f6f4a9

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Spectral_Qpoly_ne_zero

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution {scl : ℝ} (hscl : scl ≠ 0) (e₁ e₂ : ℝ) :
    ((X - C scl) * (X - C (0 : ℝ)) * Qpoly e₁ e₂).rootMultiplicity 0 =
      1 + (Qpoly e₁ e₂).rootMultiplicity 0 := by
  have hQ := Qpoly_ne_zero e₁ e₂
  have h12 : (X - C scl) * (X - C (0 : ℝ)) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  rw [rootMultiplicity_mul (mul_ne_zero h12 hQ), rootMultiplicity_mul h12,
    rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]
  simp [Ne.symm hscl]
end FriedCrossing.Spectral
