-- Prove2me | solution 1 for Eden.singularValues_frequencyEvolution_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:40.003295+00:00
-- url     : https://prove2.me/submissions/c3485111-58eb-402a-8ea0-8186bf70dd0e

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
import Theorems.Thm_Eden_ordered_singularValues_frequencyEvolution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_frequencyEvolution_zero_time
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
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.frequencyEvolution_zero_time
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
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues =
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues := by
  ext i
  by_cases hi : i < 5
  · exact congrFun (ordered_singularValues_frequencyEvolution c ν ht p) ⟨i, hi⟩
  · rw [LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le]
    all_goals simpa only [finrank_euclideanSpace_fin] using Nat.le_of_not_gt hi
end Eden
