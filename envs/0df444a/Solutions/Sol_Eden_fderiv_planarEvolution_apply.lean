-- Prove2me | solution 1 for Eden.fderiv_planarEvolution_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:57.896213+00:00
-- url     : https://prove2.me/submissions/c695f31e-9195-4c5f-b30e-305be25f561d

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_PlanarDerivative
import Theorems.Thm_Eden_contDiff_planarEvolution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_fderiv_planarX_apply
import Theorems.Thm_Eden_fderiv_planarY_apply
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
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



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PlanarSpace) :
    fderiv ℝ (planarEvolution Ω t) p v =
      !₂[planarDerivativeX Ω t (p 0) (p 1) (v 0) (v 1),
        planarDerivativeY Ω t (p 0) (p 1) (v 0) (v 1)] := by
  have hd := ((contDiff_planarEvolution Ω ht 1).differentiable one_ne_zero p).hasFDerivAt
  have hcoord (i : Fin 2) : fderiv ℝ (fun u => planarEvolution Ω t u i) p v =
      fderiv ℝ (planarEvolution Ω t) p v i := by
    have h := (PiLp.hasFDerivAt_apply 2 (planarEvolution Ω t p) i).comp p hd
    change HasFDerivAt (fun u => planarEvolution Ω t u i) _ p at h
    rw [h.fderiv]
    rfl
  ext i
  rw [← hcoord i]
  fin_cases i
  · simpa [planarEvolution] using fderiv_planarX_apply Ω ht
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [planarEvolution] using fderiv_planarY_apply Ω ht
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
end Eden
