-- Prove2me | solution 1 for Eden.fderiv_planarVectorX_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:46.876007+00:00
-- url     : https://prove2.me/submissions/085c9014-a26e-4b43-8819-548b82a102eb

import Definitions.Def_Eden_CartesianDerivative
import Mathlib.LinearAlgebra.Trace
import Definitions.Def_Eden_VectorFieldDerivative
import Theorems.Thm_Eden_hasDerivAt_q
import Theorems.Thm_Eden_deriv_q
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
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
theorem _root_.solution (Ω : ℝ)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => q (f u ^ 2 + g u ^ 2) * f u - Ω * g u) p v =
      q (f p ^ 2 + g p ^ 2) * f' v +
        2 * deriv q (f p ^ 2 + g p ^ 2) * (f p * f' v + g p * g' v) * f p - Ω * g' v := by
  have hr := (hf.pow 2).add (hg.pow 2)
  have hq := (hasDerivAt_q (f p ^ 2 + g p ^ 2)).comp_hasFDerivAt p hr
  have h := (hq.mul hf).sub (hg.const_mul Ω)
  change HasFDerivAt (fun u => q (f u ^ 2 + g u ^ 2) * f u - Ω * g u) _ p at h
  rw [h.fderiv, deriv_q]
  simp [smul_eq_mul]
  ring
end Eden
