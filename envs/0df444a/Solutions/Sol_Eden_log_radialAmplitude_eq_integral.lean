-- Prove2me | solution 1 for Eden.log_radialAmplitude_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:13.568804+00:00
-- url     : https://prove2.me/submissions/491e867f-36db-4353-927f-bb0bbbd3715b

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_hasDerivAt_log_radialAmplitude
import Theorems.Thm_Eden_continuousOn_squaredRadiusEvolution_time
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


attribute [local simp] Eden.radialAmplitude_zero_time

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.log (radialAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s) := by
  have ha : Continuous radialRate := by unfold radialRate; fun_prop
  have hcont := ha.comp_continuousOn
    ((continuousOn_squaredRadiusEvolution_time s).mono
      (show Icc 0 t ⊆ Ici 0 from fun _ h => h.1))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t)
    (fun τ hτ => hasDerivAt_log_radialAmplitude ((uIcc_of_le ht ▸ hτ).1) hs)
    (hcont.intervalIntegrable_of_Icc ht)
  simpa using hFTC.symm
end Eden
