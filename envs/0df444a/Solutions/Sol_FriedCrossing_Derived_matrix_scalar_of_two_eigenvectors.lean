-- Prove2me | solution 1 for FriedCrossing.Derived.matrix_scalar_of_two_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:02:09.680784+00:00
-- url     : https://prove2.me/submissions/8f7a0d76-c5d8-4207-8b76-25f19bb5d604

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Saturation_scalar_of_two_eigenvectors


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
namespace FriedCrossing.Derived
theorem _root_.solution (M : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (v₁ v₂ : Fin 2 → ℝ) (hind : LinearIndependent ℝ ![v₁, v₂])
    (h₁ : M *ᵥ v₁ = s • v₁) (h₂ : M *ᵥ v₂ = s • v₂) :
    M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hT : Matrix.toLin' M = s • LinearMap.id :=
    Saturation.scalar_of_two_eigenvectors (K := ℝ) (V := Fin 2 → ℝ) (Module.finrank_fin_fun ℝ)
      (Matrix.toLin' M) s v₁ v₂ hind (by rw [Matrix.toLin'_apply]; exact h₁)
      (by rw [Matrix.toLin'_apply]; exact h₂)
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  have hv := congrArg (fun T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) => T v) hT
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hv
  rw [hv, Matrix.toLin'_apply]
  ext i
  fin_cases i <;> simp
end FriedCrossing.Derived
