-- Prove2me | solution 1 for Eden.normalizedLogSingularValues_periodic_le_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:38.457318+00:00
-- url     : https://prove2.me/submissions/d070ea62-a60c-4eb4-8e3a-b0749df8dbaa

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_mem_positiveReturnSet_iff
import Theorems.Thm_Eden_normalizedLogSingularValues_of_stationary_radii
import Theorems.Thm_Eden_normalizedLogSingularValues_outer_circle
import Theorems.Thm_Eden_normalizedLogSingularValues_unit_circle
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_spectrumInterpolation_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.spectrumInterpolation_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace}
    (hp : p ∈ periodicEquilibriumSet c) :
    ∀ i : Fin 5, normalizedLogSingularValues c t p i ≤ ![2, 0, -2, -2, -c] i := by
  rw [periodicEquilibriumSet_eq_positiveReturnSet (show 0 < c by linarith)] at hp
  rcases (mem_positiveReturnSet_iff (by linarith) p).mp hp with rfl | h | h | h | h
  · have hzero : normalizedLogSingularValues c t 0 = ![-2, -2, -2, -2, -c] := by
      rw [normalizedLogSingularValues_of_stationary_radii c ht 0
        (Or.inl (by simp [radiusSq₁])) (Or.inl (by simp [radiusSq₂]))]
      simpa [radiusSq₁, radiusSq₂] using descending_radiusPairSpectrum_zero_zero hc
    rw [hzero]
    intro i; fin_cases i <;> norm_num
  · rw [normalizedLogSingularValues_unit_circle hc ht (Or.inl h)]
    exact fun _ => le_rfl
  · rw [normalizedLogSingularValues_outer_circle hc ht (Or.inl h)]
    intro i; fin_cases i <;> norm_num
  · rw [normalizedLogSingularValues_unit_circle hc ht (Or.inr h)]
    exact fun _ => le_rfl
  · rw [normalizedLogSingularValues_outer_circle hc ht (Or.inr h)]
    intro i; fin_cases i <;> norm_num
end Eden
