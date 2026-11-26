-- Prove2me | solution 1 for Eden.fderiv_planarY_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:43.441731+00:00
-- url     : https://prove2.me/submissions/bee74232-6fbb-4816-b15c-535fa3a56ae8

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Definitions.Def_Eden_CartesianDerivative
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_contDiffAt_planarAmplitude
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => planarY Ω t (f u) (g u)) p v =
      planarDerivativeY Ω t (f p) (g p) (f' v) (g' v) := by
  have hr := (hf.pow 2).add (hg.pow 2)
  have ha := (contDiffAt_planarAmplitude ht
    (add_nonneg (sq_nonneg (f p)) (sq_nonneg (g p))) 1).differentiableAt_one.hasDerivAt
  have hcomp := ha.comp_hasFDerivAt p hr
  have hrot := (hf.mul_const (Real.sin (Ω * t))).add (hg.mul_const (Real.cos (Ω * t)))
  have hprod := hcomp.mul hrot
  change HasFDerivAt (fun u => planarY Ω t (f u) (g u)) _ p at hprod
  rw [hprod.fderiv]
  simp [planarDerivativeY, smul_eq_mul]
  ring
end Eden
