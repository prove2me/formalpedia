-- Prove2me | solution 1 for Eden.singularValues_fderiv_planarEvolution_integrals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:32.742838+00:00
-- url     : https://prove2.me/submissions/86320929-e96e-4850-90c5-5dc4e2d8ad7f

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
import Theorems.Thm_Eden_singularValues_fderiv_planarEvolution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_eq_exp_integral
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarDiagonal_apply
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_planar_radius_sq
import Theorems.Thm_Eden_radialAmplitude_eq_exp_integral
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarDiagonal_apply
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Polynomial
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PlanarSpace) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      {Real.exp (∫ τ in (0 : ℝ)..t, radialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)),
       Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2))} := by
  rw [singularValues_fderiv_planarEvolution Ω ht p]
  have hr (f : ℝ → ℝ) :
      (∫ τ in (0 : ℝ)..t, f (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)) =
        ∫ τ in (0 : ℝ)..t, f (squaredRadiusEvolution τ (p 0 ^ 2 + p 1 ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    have hτ₀ : 0 ≤ τ := (Set.uIcc_of_le ht ▸ hτ).1
    change f (planarX Ω τ (p 0) (p 1) ^ 2 + planarY Ω τ (p 0) (p 1) ^ 2) = _
    rw [planar_radius_sq Ω hτ₀]
  rw [hr radialRate, hr tangentialRate]
  have hpos := add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))
  rw [← radialAmplitude_eq_exp_integral ht hpos, ← planarAmplitude_eq_exp_integral ht hpos]
  simp [Fin.univ_succ, planarFactors]
end Eden
