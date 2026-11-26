-- Prove2me | solution 1 for Eden.fderiv_evolution_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:03.582615+00:00
-- url     : https://prove2.me/submissions/1ea8e3c6-51bf-4cd4-8979-add4bfd68ac3

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Definitions.Def_Eden_CartesianDerivative
import Theorems.Thm_Eden_fderiv_planarX_apply
import Theorems.Thm_Eden_fderiv_planarY_apply
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_contDiff_evolution
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
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace) :
    fderiv ℝ (evolution c t) p v =
      !₂[planarDerivativeX 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeY 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeX (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         planarDerivativeY (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         Real.exp (-c * t) * v 4] := by
  have hd := ((contDiff_evolution c ht 1).differentiable one_ne_zero p).hasFDerivAt
  have hcoord (i : Fin 5) : fderiv ℝ (fun u => evolution c t u i) p v =
      fderiv ℝ (evolution c t) p v i := by
    have h := (PiLp.hasFDerivAt_apply 2 (evolution c t p) i).comp p hd
    change HasFDerivAt (fun u => evolution c t u i) _ p at h
    rw [h.fderiv]
    rfl
  ext i
  rw [← hcoord i]
  fin_cases i
  · simpa [evolution] using fderiv_planarX_apply 1 ht
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [evolution] using fderiv_planarY_apply 1 ht
      (PiLp.hasFDerivAt_apply 2 p 0) (PiLp.hasFDerivAt_apply 2 p 1) v
  · simpa [evolution] using fderiv_planarX_apply (Real.sqrt 2) ht
      (PiLp.hasFDerivAt_apply 2 p 2) (PiLp.hasFDerivAt_apply 2 p 3) v
  · simpa [evolution] using fderiv_planarY_apply (Real.sqrt 2) ht
      (PiLp.hasFDerivAt_apply 2 p 2) (PiLp.hasFDerivAt_apply 2 p 3) v
  · have hw := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 4).const_mul (Real.exp (-c * t))
    simpa [evolution] using congrArg (fun L : PhaseSpace →L[ℝ] ℝ => L v) hw.fderiv
end Eden
