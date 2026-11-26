-- Prove2me | solution 1 for Eden.tendsto_log_exterior_coordinate_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:39.581853+00:00
-- url     : https://prove2.me/submissions/8ddd62fb-a092-425c-82b7-29a6d0f57a3a

import Definitions.Def_Eden_ExteriorGeometry
import Definitions.Def_Eden_LogarithmicSums
import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_ExteriorLimits
import Theorems.Thm_Eden_exteriorFactor_pos
import Theorems.Thm_Eden_tendsto_log_exteriorFactor_div
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
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
theorem _root_.solution (k : ℕ) (c : ℝ) (p : PhaseSpace)
    (s : ExteriorIndex k) {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun t => Real.log ((exteriorFactor k (derivativeFactors c t p) s * a) ^ 2) / t)
      atTop (𝓝 (2 * exteriorRate k c p s)) := by
  have hc : Tendsto (fun t : ℝ => Real.log a / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := ((tendsto_log_exteriorFactor_div k c p s).add hc).const_mul 2
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.log_pow, Real.log_mul (exteriorFactor_pos k c ht p s).ne' ha]
  push_cast
  ring
end Eden
