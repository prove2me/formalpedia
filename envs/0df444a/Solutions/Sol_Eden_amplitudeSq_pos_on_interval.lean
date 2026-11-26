-- Prove2me | solution 1 for Eden.amplitudeSq_pos_on_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:19:39.460389+00:00
-- url     : https://prove2.me/submissions/5be6eb76-00ff-44a9-9098-eee07872466a

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
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
theorem _root_.solution (t : ℝ) {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    0 < amplitudeSq t s := by
  have hD := radialDiscriminant_pos_on_interval t hs₀ hs₂
  have hR := Real.sqrt_pos.2 hD
  have hsq := Real.sq_sqrt hD.le
  have he := Real.exp_pos (-4 * t)
  have hu : (s - 1) ^ 2 ≤ 1 := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hu) he.le
  have hbound : (s - 1) ^ 2 ≤ radialDiscriminant t s := by
    dsimp [radialDiscriminant]
    nlinarith
  have hRge : 1 - s ≤ Real.sqrt (radialDiscriminant t s) := by
    nlinarith
  have hnum : 0 < Real.sqrt (radialDiscriminant t s) + 1 +
      (s - 2) * (1 - Real.exp (-4 * t)) := by
    rcases lt_or_eq_of_le hs₂ with hs₂ | hs₂
    · have hp := mul_pos (sub_pos.mpr hs₂) he
      nlinarith
    · subst s
      nlinarith
  have hden : 0 < Real.sqrt (radialDiscriminant t s) + 1 := by linarith
  have hquot : -1 < (s - 2) * (1 - Real.exp (-4 * t)) /
      (Real.sqrt (radialDiscriminant t s) + 1) :=
    (lt_div_iff₀ hden).2 (by linarith)
  exact div_pos (by linarith) hR
end Eden
