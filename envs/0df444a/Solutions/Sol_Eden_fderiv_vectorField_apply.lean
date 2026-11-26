-- Prove2me | solution 1 for Eden.fderiv_vectorField_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:45.521057+00:00
-- url     : https://prove2.me/submissions/cd4a9168-92b4-4eb9-987c-1b8e9f0beacb

import Definitions.Def_Eden_CartesianDerivative
import Mathlib.LinearAlgebra.Trace
import Definitions.Def_Eden_VectorFieldDerivative
import Theorems.Thm_Eden_fderiv_planarVectorX_apply
import Theorems.Thm_Eden_fderiv_planarVectorY_apply
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_contDiff_vectorField
import Theorems.Thm_Eden_evolution_zero_time
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
theorem _root_.solution (c : ℝ) (p v : PhaseSpace) :
    fderiv ℝ (vectorField c) p v =
      !₂[q (radiusSq₁ p) * v 0 + 2 * deriv q (radiusSq₁ p) *
          (p 0 * v 0 + p 1 * v 1) * p 0 - v 1,
        q (radiusSq₁ p) * v 1 + 2 * deriv q (radiusSq₁ p) *
          (p 0 * v 0 + p 1 * v 1) * p 1 + v 0,
        q (radiusSq₂ p) * v 2 + 2 * deriv q (radiusSq₂ p) *
          (p 2 * v 2 + p 3 * v 3) * p 2 - Real.sqrt 2 * v 3,
        q (radiusSq₂ p) * v 3 + 2 * deriv q (radiusSq₂ p) *
          (p 2 * v 2 + p 3 * v 3) * p 3 + Real.sqrt 2 * v 2,
        -c * v 4] := by
  have hd := ((contDiff_vectorField c 1).differentiable one_ne_zero p).hasFDerivAt
  have hcoord (i : Fin 5) : fderiv ℝ (fun u => vectorField c u i) p v =
      fderiv ℝ (vectorField c) p v i := by
    have h := (PiLp.hasFDerivAt_apply 2 (vectorField c p) i).comp p hd
    change HasFDerivAt (fun u => vectorField c u i) _ p at h
    rw [h.fderiv]
    rfl
  ext i
  rw [← hcoord i]
  fin_cases i
  · simpa [vectorField, radiusSq₁] using fderiv_planarVectorX_apply 1
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [vectorField, radiusSq₁] using fderiv_planarVectorY_apply 1
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [vectorField, radiusSq₂] using fderiv_planarVectorX_apply (Real.sqrt 2)
      (PiLp.hasFDerivAt_apply 2 p 2) (PiLp.hasFDerivAt_apply 2 p 3) v
  · simpa [vectorField, radiusSq₂] using fderiv_planarVectorY_apply (Real.sqrt 2)
      (PiLp.hasFDerivAt_apply 2 p 2) (PiLp.hasFDerivAt_apply 2 p 3) v
  · have hw := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 4).const_mul (-c)
    simpa [vectorField] using congrArg (fun L : PhaseSpace →L[ℝ] ℝ => L v) hw.fderiv
end Eden
