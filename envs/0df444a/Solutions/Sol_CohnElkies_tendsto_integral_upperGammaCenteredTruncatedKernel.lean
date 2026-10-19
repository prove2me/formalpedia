-- Prove2me | solution 1 for CohnElkies.tendsto_integral_upperGammaCenteredTruncatedKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/4332eff4-9306-4f05-b7b9-99ecaf388084

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaCenteredKernel_integrable
import Theorems.Thm_CohnElkies_upperGammaCenteredGeometricLimit_eq_kernel

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
          upperGammaCenteredTruncatedKernel ℓ η T n a)
      atTop (𝓝 (upperGammaCenteredPhase ℓ η T)) := by
  unfold upperGammaCenteredPhase
  refine tendsto_integral_of_dominated_convergence
    (fun a => ‖upperGammaCenteredKernel ℓ η T a‖) ?_
    ((upperGammaCenteredKernel_integrable hℓ hη T).norm) ?_ ?_
  · intro n
    apply Measurable.aestronglyMeasurable
    unfold upperGammaCenteredTruncatedKernel
      upperCenteredLaplaceKernel upperImaginaryExp
    fun_prop
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    have hq0 : 0 ≤ Real.exp (-(2 * a / ℓ)) :=
      (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * a / ℓ)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have hp : 0 < 2 * a / ℓ :=
        div_pos (mul_pos (by norm_num) ha) hℓ
      linarith
    have hsum :
        (∑ k ∈ Finset.range (n + 1),
          Real.exp (-(2 * a / ℓ)) ^ k) ≤
          (1 - Real.exp (-(2 * a / ℓ)))⁻¹ :=
      sum_le_hasSum (Finset.range (n + 1))
        (fun k hk => pow_nonneg hq0 k)
        (hasSum_geometric_of_lt_one hq0 hq1)
    have hsum0 :
        0 ≤ ∑ k ∈ Finset.range (n + 1),
          Real.exp (-(2 * a / ℓ)) ^ k :=
      Finset.sum_nonneg
        (fun k hk => pow_nonneg hq0 k)
    have hinv0 :
        0 ≤ (1 - Real.exp (-(2 * a / ℓ)))⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hq1.le)
    change
      ‖upperCenteredLaplaceKernel η T a *
          ((∑ k ∈ Finset.range (n + 1),
            Real.exp (-(2 * a / ℓ)) ^ k : ℝ) : ℂ)‖ ≤
        ‖upperGammaCenteredKernel ℓ η T a‖
    rw [← upperGammaCenteredGeometricLimit_eq_kernel,
      norm_mul, norm_mul,
      Complex.norm_of_nonneg hsum0,
      Complex.norm_of_nonneg hinv0]
    exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    have hq0 : 0 ≤ Real.exp (-(2 * a / ℓ)) :=
      (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * a / ℓ)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have hp : 0 < 2 * a / ℓ :=
        div_pos (mul_pos (by norm_num) ha) hℓ
      linarith
    have hgeo :=
      (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat
    have hshift := hgeo.comp (tendsto_add_atTop_nat 1)
    have hlimit :=
      (tendsto_const_nhds
        (x := upperCenteredLaplaceKernel η T a)).mul
          hshift.ofReal
    simpa only [upperGammaCenteredTruncatedKernel,
      upperGammaCenteredGeometricLimit_eq_kernel,
      Function.comp_apply] using! hlimit
end CohnElkies
