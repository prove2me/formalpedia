-- Prove2me | solution 1 for Eden.log_planarAmplitude_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:24.386947+00:00
-- url     : https://prove2.me/submissions/d2df38fd-47c3-47a2-b828-61b43f41d08b

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_SingularValues
import Definitions.Def_Eden_FactorBounds
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_continuousOn_squaredRadiusEvolution_time
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_log_planarAmplitude_eq_integral
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
import Theorems.Thm_Eden_squaredRadiusEvolution_le_two_iff
import Theorems.Thm_Eden_squaredRadiusEvolution_nonneg
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_tangentialRate_lower_bound
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
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


section
noncomputable section
open Set
namespace Eden
private theorem rate_intervalIntegrable {f : ℝ → ℝ} (hf : Continuous f)
    {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    IntervalIntegrable (fun τ => f (squaredRadiusEvolution τ s))
      MeasureTheory.volume 0 t :=
  (hf.comp_continuousOn ((continuousOn_squaredRadiusEvolution_time s).mono
    (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1))).intervalIntegrable_of_Icc ht
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t)
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : -2 * t ≤ Real.log (planarAmplitude t s) := by
  rw [log_planarAmplitude_eq_integral ht hs₀]
  have hb : Continuous tangentialRate := by unfold tangentialRate; fun_prop
  have hi := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const (c := (-2 : ℝ))) (rate_intervalIntegrable hb ht s)
    (fun τ hτ => tangentialRate_lower_bound
      (squaredRadiusEvolution_nonneg hτ.1 hs₀)
      ((squaredRadiusEvolution_le_two_iff hτ.1).2 hs₂))
  simpa [mul_comm] using hi
end Eden
