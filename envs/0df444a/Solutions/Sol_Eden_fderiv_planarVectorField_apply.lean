-- Prove2me | solution 1 for Eden.fderiv_planarVectorField_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:20.643792+00:00
-- url     : https://prove2.me/submissions/a42676d6-d293-4058-a85b-9a7ebecd29f7

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_PlanarVectorField
import Theorems.Thm_Eden_contDiff_planarVectorField
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_fderiv_planarVectorX_apply
import Theorems.Thm_Eden_fderiv_planarVectorY_apply
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
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
theorem _root_.solution (Ω : ℝ) (p v : PlanarSpace) :
    fderiv ℝ (planarVectorField Ω) p v =
      !₂[q (p 0 ^ 2 + p 1 ^ 2) * v 0 + 2 * deriv q (p 0 ^ 2 + p 1 ^ 2) *
          (p 0 * v 0 + p 1 * v 1) * p 0 - Ω * v 1,
        q (p 0 ^ 2 + p 1 ^ 2) * v 1 + 2 * deriv q (p 0 ^ 2 + p 1 ^ 2) *
          (p 0 * v 0 + p 1 * v 1) * p 1 + Ω * v 0] := by
  have hd := ((contDiff_planarVectorField Ω 1).differentiable one_ne_zero p).hasFDerivAt
  have hcoord (i : Fin 2) : fderiv ℝ (fun u => planarVectorField Ω u i) p v =
      fderiv ℝ (planarVectorField Ω) p v i := by
    have h := (PiLp.hasFDerivAt_apply 2 (planarVectorField Ω p) i).comp p hd
    change HasFDerivAt (fun u => planarVectorField Ω u i) _ p at h
    rw [h.fderiv]
    rfl
  ext i
  rw [← hcoord i]
  fin_cases i
  · simpa [planarVectorField] using fderiv_planarVectorX_apply Ω
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [planarVectorField] using fderiv_planarVectorY_apply Ω
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
end Eden
