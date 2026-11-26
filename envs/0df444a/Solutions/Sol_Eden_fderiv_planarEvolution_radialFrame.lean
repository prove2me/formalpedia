-- Prove2me | solution 1 for Eden.fderiv_planarEvolution_radialFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:58.913369+00:00
-- url     : https://prove2.me/submissions/b906dc61-f01b-41c9-9f47-2da048df8d40

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_PlanarDerivative
import Theorems.Thm_Eden_fderiv_planarEvolution_apply
import Theorems.Thm_Eden_planarDiagonal_apply
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarDerivativeX_on_radialFrame
import Theorems.Thm_Eden_planarDerivativeY_on_radialFrame
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_radius_mul_radialCos
import Theorems.Thm_Eden_radius_mul_radialSin
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
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


attribute [local simp] Eden.planarDiagonal_apply

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PlanarSpace) :
    fderiv ℝ (planarEvolution Ω t) p (planarRadialFrame p v) =
      planarAngularRotation Ω t (planarRadialFrame p (planarDiagonal (planarFactors t p) v)) := by
  have hsq := Real.sq_sqrt (add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1)))
  have hx := planarDerivativeX_on_radialFrame Ω ht
    (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (v 0) (v 1) (radialCos_sq_add_radialSin_sq _ _)
  have hy := planarDerivativeY_on_radialFrame Ω ht
    (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (v 0) (v 1) (radialCos_sq_add_radialSin_sq _ _)
  simp only [radius_mul_radialCos, radius_mul_radialSin, hsq] at hx hy
  rw [fderiv_planarEvolution_apply Ω ht]
  ext i
  fin_cases i
  · simpa [planarRadialFrame, planarAngularRotation, rotatePlane, planarDiagonal,
      planarFactors, mul_comm] using hx
  · simpa [planarRadialFrame, planarAngularRotation, rotatePlane, planarDiagonal,
      planarFactors, mul_comm] using hy
end Eden
