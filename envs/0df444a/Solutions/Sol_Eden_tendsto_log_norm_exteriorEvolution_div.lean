-- Prove2me | solution 1 for Eden.tendsto_log_norm_exteriorEvolution_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:30.779303+00:00
-- url     : https://prove2.me/submissions/d0d1bab1-671a-41cb-b834-7753e18d38e9

import Definitions.Def_Eden_ExteriorGeometry
import Definitions.Def_Eden_LogarithmicSums
import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_ExteriorLimits
import Theorems.Thm_Eden_exteriorFactor_pos
import Theorems.Thm_Eden_norm_sq_exteriorEvolution_support
import Theorems.Thm_Eden_tendsto_log_exterior_coordinate_sq_div
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
import Theorems.Thm_Eden_tendsto_log_finset_sum_div
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
theorem _root_.solution {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    Tendsto (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 ((exteriorSupport k p v).sup' (exteriorSupport_nonempty p hv) (exteriorRate k c p))) := by
  classical
  let s := exteriorSupport k p v
  have hs : s.Nonempty := exteriorSupport_nonempty p hv
  let f := fun j t => (exteriorFactor k (derivativeFactors c t p) j *
    exteriorInitialCoordinates k p v j) ^ 2
  have ha (j : ExteriorIndex k) (hj : j ∈ s) : exteriorInitialCoordinates k p v j ≠ 0 :=
    (Finset.mem_filter.mp hj).2
  have hp (j : ExteriorIndex k) (hj : j ∈ s) : ∀ᶠ t in atTop, 0 < f j t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact sq_pos_of_ne_zero (mul_ne_zero (exteriorFactor_pos k c ht p j).ne' (ha j hj))
  have h := tendsto_log_finset_sum_div s hs f (fun j => 2 * exteriorRate k c p j) hp
    (fun j hj => tendsto_log_exterior_coordinate_sq_div k c p j (ha j hj))
  have hsup : s.sup' hs (fun j => 2 * exteriorRate k c p j) =
      2 * s.sup' hs (exteriorRate k c p) := by
    symm
    exact Finset.apply_sup'_eq_sup'_comp hs (fun r : ℝ => 2 * r)
      (fun x y => by exact mul_max_of_nonneg x y (show (0 : ℝ) ≤ 2 by norm_num))
  rw [hsup] at h
  have hhalf := h.div_const 2
  simp only [mul_div_cancel_left₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] at hhalf
  apply hhalf.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  symm
  change Real.log ‖exteriorEvolution k c t p v‖ / t =
    (Real.log (∑ j ∈ exteriorSupport k p v,
      (exteriorFactor k (derivativeFactors c t p) j * exteriorInitialCoordinates k p v j) ^ 2) / t) / 2
  rw [← norm_sq_exteriorEvolution_support k c ht p v, Real.log_pow]
  push_cast
  ring
end Eden
