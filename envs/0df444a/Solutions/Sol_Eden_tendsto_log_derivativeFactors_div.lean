-- Prove2me | solution 1 for Eden.tendsto_log_derivativeFactors_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:41.815112+00:00
-- url     : https://prove2.me/submissions/e495b1ee-9e90-4dfc-b90d-8e396fd7375b

import Definitions.Def_Eden_RealTimeAverages
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FactorLimits
import Theorems.Thm_Eden_tendsto_log_radialAmplitude_div
import Theorems.Thm_Eden_tendsto_log_planarAmplitude_div
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
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d
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
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t => Real.log (derivativeFactors c t p i) / t) atTop
      (𝓝 (factorExponents c p i)) := by
  fin_cases i
  · simpa [derivativeFactors, factorExponents] using
      tendsto_log_radialAmplitude_div (radiusSq₁_nonneg p)
  · simpa [derivativeFactors, factorExponents] using
      tendsto_log_planarAmplitude_div (radiusSq₁_nonneg p)
  · simpa [derivativeFactors, factorExponents] using
      tendsto_log_radialAmplitude_div (radiusSq₂_nonneg p)
  · simpa [derivativeFactors, factorExponents] using
      tendsto_log_planarAmplitude_div (radiusSq₂_nonneg p)
  · apply (tendsto_const_nhds (x := -c)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [derivativeFactors]
    field_simp
end Eden
