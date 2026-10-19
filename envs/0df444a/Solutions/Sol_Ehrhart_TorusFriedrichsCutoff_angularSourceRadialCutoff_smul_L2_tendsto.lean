-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsCutoff.angularSourceRadialCutoff_smul_L2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/97f4d509-6aab-4aa8-a5e6-46f917f61820

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral
import Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_angularSourceRadialCutoff_smul_squared_error_integrals_tendsto_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusFriedrichsCutoff
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters JetEnvelopeRightDerivative EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff
namespace Ehrhart.TorusFriedrichsCutoff
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    {F : LogTorus n → E}
    (hF : MemLp F 2 (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        (angularSourceRadialCutoff_smul_memLp hF m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • F q))
      atTop (nhds (hF.toLp F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnormsq (m : ℕ) :
      ‖(angularSourceRadialCutoff_smul_memLp hF m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • F q) -
        hF.toLp F‖ ^ 2 =
      ∫ q : LogTorus n,
        ‖(sourceRadialCutoff m q : ℂ) • F q - F q‖ ^ 2
        ∂(angularWeightedTorusMeasure a) := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards
      [MeasureTheory.Lp.coeFn_sub
        ((angularSourceRadialCutoff_smul_memLp hF m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • F q))
        (hF.toLp F),
       (angularSourceRadialCutoff_smul_memLp hF m).coeFn_toLp,
       hF.coeFn_toLp]
      with q hsub hcut hfull
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hcut, hfull]
  have hsq :
      Tendsto
        (fun m : ℕ =>
          ‖(angularSourceRadialCutoff_smul_memLp hF m).toLp
              (fun q : LogTorus n =>
                (sourceRadialCutoff m q : ℂ) • F q) -
            hF.toLp F‖ ^ 2)
        atTop (nhds 0) := by
    simpa only [hnormsq] using
      angularSourceRadialCutoff_smul_squared_error_integrals_tendsto_zero hF
  simpa [Real.sqrt_sq_eq_abs] using hsq.sqrt
end Ehrhart.TorusFriedrichsCutoff
