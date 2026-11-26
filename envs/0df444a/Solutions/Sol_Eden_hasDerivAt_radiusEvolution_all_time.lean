-- Prove2me | solution 1 for Eden.hasDerivAt_radiusEvolution_all_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:52:46.855539+00:00
-- url     : https://prove2.me/submissions/e045ca27-5571-4315-813a-dffc2711076d

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
import Theorems.Thm_Eden_amplitudeSq_pos_on_interval
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution_of_discriminant_pos
import Theorems.Thm_Eden_mul_amplitudeSq_of_discriminant_pos
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_pos_on_interval
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_radiusEvolution_at_one
import Theorems.Thm_Eden_radiusEvolution_at_sqrt_two
import Theorems.Thm_Eden_radiusEvolution_at_zero
import Theorems.Thm_Eden_radiusEvolution_zero_time
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
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.radiusEvolution_at_one
attribute [local simp] Eden.radiusEvolution_at_sqrt_two
attribute [local simp] Eden.radiusEvolution_at_zero
attribute [local simp] Eden.radiusEvolution_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (t : ℝ) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₂ : r ≤ Real.sqrt 2) :
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t := by
  rcases eq_or_lt_of_le hr₀ with hr | hr
  · subst r
    simpa [radialField] using hasDerivAt_const t (0 : ℝ)
  have hs₂ : r ^ 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hD := radialDiscriminant_pos_on_interval t (sq_nonneg r) hs₂
  have hB := amplitudeSq_pos_on_interval t (sq_nonneg r) hs₂
  have hpos : 0 < squaredRadiusEvolution t (r ^ 2) := by
    rw [← mul_amplitudeSq_of_discriminant_pos hD]
    exact mul_pos (sq_pos_of_pos hr) hB
  have hR : 0 < radiusEvolution t r := Real.sqrt_pos.2 hpos
  have hsq : radiusEvolution t r ^ 2 = squaredRadiusEvolution t (r ^ 2) :=
    Real.sq_sqrt hpos.le
  apply ((hasDerivAt_squaredRadiusEvolution_of_discriminant_pos hD).sqrt hpos.ne').congr_deriv
  change (-2 * squaredRadiusEvolution t (r ^ 2) *
      (squaredRadiusEvolution t (r ^ 2) - 1) *
      (squaredRadiusEvolution t (r ^ 2) - 2)) /
      (2 * radiusEvolution t r) = radialField (radiusEvolution t r)
  rw [← hsq]
  unfold radialField
  field_simp
end Eden
