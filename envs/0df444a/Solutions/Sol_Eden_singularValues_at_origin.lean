-- Prove2me | solution 1 for Eden.singularValues_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:36.479797+00:00
-- url     : https://prove2.me/submissions/2a912419-6de4-462b-a947-b665f64db68a

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_SingularValues
import Mathlib.Data.List.Sort
import Mathlib.Order.Fin.Basic
import Definitions.Def_Eden_OrderedStationarySpectrum
import Theorems.Thm_Eden_antitone_eq_of_multiset_eq
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_derivativeFactors_at_origin
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValues_fderiv_evolution
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
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



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 2 ≤ c) (ht : 0 ≤ t) :
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) 0).toLinearMap.singularValues i) =
      ![Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
        Real.exp (-2 * t), Real.exp (-c * t)] := by
  let A := (fderiv ℝ (evolution c t) 0).toLinearMap
  have hlow : Real.exp (-c * t) ≤ Real.exp (-2 * t) := Real.exp_le_exp.mpr (by nlinarith)
  apply antitone_eq_of_multiset_eq
  · exact fun i j hij => A.singularValues_antitone hij
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp_all
  · rw [singularValues_fderiv_evolution c ht 0, derivativeFactors_at_origin c ht]
end Eden
