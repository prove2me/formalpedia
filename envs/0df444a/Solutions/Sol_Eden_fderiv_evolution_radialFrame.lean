-- Prove2me | solution 1 for Eden.fderiv_evolution_radialFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:19.564051+00:00
-- url     : https://prove2.me/submissions/a007f1aa-1a91-4d5e-91db-1cd3d3abdb77

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_fderiv_evolution_apply
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


attribute [local simp] Eden.diagonalLinear_apply

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace) :
    fderiv ℝ (evolution c t) p (radialFrame p v) =
      angularRotation t (radialFrame p (diagonalLinear (derivativeFactors c t p) v)) := by
  have hsq₁ := Real.sq_sqrt (add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1)))
  have hsq₂ := Real.sq_sqrt (add_nonneg (sq_nonneg (p 2)) (sq_nonneg (p 3)))
  have hX₁ := planarDerivativeX_on_radialFrame 1 ht
    (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (v 0) (v 1) (radialCos_sq_add_radialSin_sq _ _)
  have hY₁ := planarDerivativeY_on_radialFrame 1 ht
    (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (v 0) (v 1) (radialCos_sq_add_radialSin_sq _ _)
  have hX₂ := planarDerivativeX_on_radialFrame (Real.sqrt 2) ht
    (radialCos (p 2) (p 3)) (radialSin (p 2) (p 3))
    (Real.sqrt (p 2 ^ 2 + p 3 ^ 2)) (v 2) (v 3) (radialCos_sq_add_radialSin_sq _ _)
  have hY₂ := planarDerivativeY_on_radialFrame (Real.sqrt 2) ht
    (radialCos (p 2) (p 3)) (radialSin (p 2) (p 3))
    (Real.sqrt (p 2 ^ 2 + p 3 ^ 2)) (v 2) (v 3) (radialCos_sq_add_radialSin_sq _ _)
  simp only [radius_mul_radialCos, radius_mul_radialSin, hsq₁, one_mul] at hX₁ hY₁
  simp only [radius_mul_radialCos, radius_mul_radialSin, hsq₂] at hX₂ hY₂
  rw [fderiv_evolution_apply c ht]
  ext i
  fin_cases i
  · simpa [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors,
      radiusSq₁, mul_comm] using hX₁
  · simpa [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors,
      radiusSq₁, mul_comm] using hY₁
  · simpa [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors,
      radiusSq₂, mul_comm] using hX₂
  · simpa [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors,
      radiusSq₂, mul_comm] using hY₂
  · simp [radialFrame, angularRotation, rotateBlocks, diagonalLinear, derivativeFactors]
end Eden
