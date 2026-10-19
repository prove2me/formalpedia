-- Prove2me | solution 1 for CohnElkies.tendsto_integral_upperGammaTruncatedDampingIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/2638a1f0-d82e-4a1b-847a-79bab412ed13

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaDampingIntegrand_integrable
import Theorems.Thm_CohnElkies_upperGammaGeometricLimit_eq_integrand

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ a : ℝ in Ioi 0,
          upperGammaTruncatedDampingIntegrand ℓ η T n a)
      atTop (𝓝 (upperGammaDamping ℓ η T)) := by
  unfold upperGammaDamping
  refine tendsto_integral_of_dominated_convergence
    (upperGammaDampingIntegrand ℓ η T) ?_
    (upperGammaDampingIntegrand_integrable hℓ hη T) ?_ ?_
  · intro n
    apply Measurable.aestronglyMeasurable
    unfold upperGammaTruncatedDampingIntegrand
      upperCosLaplaceKernel
    fun_prop
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    have hq0 : 0 ≤ Real.exp (-(2 * a / ℓ)) :=
      (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * a / ℓ)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have : 0 < 2 * a / ℓ :=
        div_pos (mul_pos (by norm_num) ha) hℓ
      linarith
    have hbase : 0 ≤ upperCosLaplaceKernel η T a := by
      unfold upperCosLaplaceKernel
      exact div_nonneg
        (mul_nonneg
          (sub_nonneg.mpr (Real.cos_le_one _))
          (Real.exp_pos _).le) ha.le
    have hsum :
        (∑ k ∈ Finset.range (n + 1),
          Real.exp (-(2 * a / ℓ)) ^ k) ≤
          (1 - Real.exp (-(2 * a / ℓ)))⁻¹ := by
      exact sum_le_hasSum (Finset.range (n + 1))
        (fun k hk => pow_nonneg hq0 k)
        (hasSum_geometric_of_lt_one hq0 hq1)
    have hpartial : 0 ≤
        upperGammaTruncatedDampingIntegrand ℓ η T n a := by
      unfold upperGammaTruncatedDampingIntegrand
      exact mul_nonneg hbase
        (Finset.sum_nonneg (fun k hk => pow_nonneg hq0 k))
    rw [Real.norm_eq_abs, abs_of_nonneg hpartial]
    calc
      upperGammaTruncatedDampingIntegrand ℓ η T n a =
          upperCosLaplaceKernel η T a *
            ∑ k ∈ Finset.range (n + 1),
              Real.exp (-(2 * a / ℓ)) ^ k := rfl
      _ ≤ upperCosLaplaceKernel η T a *
          (1 - Real.exp (-(2 * a / ℓ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hsum hbase
      _ = upperGammaDampingIntegrand ℓ η T a :=
        upperGammaGeometricLimit_eq_integrand ℓ η T a
  · filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    have hq0 : 0 ≤ Real.exp (-(2 * a / ℓ)) :=
      (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * a / ℓ)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have : 0 < 2 * a / ℓ :=
        div_pos (mul_pos (by norm_num) ha) hℓ
      linarith
    have hgeo :=
      (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat
    have hshift := hgeo.comp (tendsto_add_atTop_nat 1)
    have hlimit :=
      Filter.Tendsto.mul
        (tendsto_const_nhds
          (x := upperCosLaplaceKernel η T a)) hshift
    simpa [upperGammaTruncatedDampingIntegrand,
      upperGammaGeometricLimit_eq_integrand] using! hlimit
end CohnElkies
