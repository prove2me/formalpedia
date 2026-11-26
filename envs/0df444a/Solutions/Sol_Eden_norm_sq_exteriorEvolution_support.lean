-- Prove2me | solution 1 for Eden.norm_sq_exteriorEvolution_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:19.973297+00:00
-- url     : https://prove2.me/submissions/c76f84b5-1384-4964-a8bf-57b9b105a194

import Definitions.Def_Eden_ExteriorGeometry
import Definitions.Def_Eden_LogarithmicSums
import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_ExteriorLimits
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_norm_sq_exteriorEvolution
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
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s ∈ exteriorSupport k p v,
      (exteriorFactor k (derivativeFactors c t p) s * exteriorInitialCoordinates k p v s) ^ 2 := by
  classical
  rw [norm_sq_exteriorEvolution k c ht]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s _ hs
  have hz : exteriorInitialCoordinates k p v s = 0 := by simpa [exteriorSupport] using hs
  simp [hz]
end Eden
