-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsCutoff.angularSourceRadialCutoff_smul_squared_error_integrals_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/f456dae5-2240-4f98-b30e-717340dc4905

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreDensity_sourceRadialCutoff_eventually_one

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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : LogTorus n → E}
    (hF : MemLp F 2 (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) • F q - F q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  have hbound : Integrable
      (fun q : LogTorus n => ‖F q‖ ^ 2)
      (angularWeightedTorusMeasure a) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hF.aestronglyMeasurable).mp hF
  have hdom := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := angularWeightedTorusMeasure a)
    (F := fun m : ℕ =>
      fun q : LogTorus n =>
        ‖(sourceRadialCutoff m q : ℂ) • F q - F q‖ ^ 2)
    (f := fun _ : LogTorus n => (0 : ℝ))
    (fun q : LogTorus n => ‖F q‖ ^ 2)
    (by
      intro m
      have hscalar : Continuous
          (fun q : LogTorus n => (sourceRadialCutoff m q : ℂ)) :=
        Complex.continuous_ofReal.comp
          (continuous_sourceRadialCutoff m)
      exact ((hscalar.aestronglyMeasurable.smul
        hF.aestronglyMeasurable).sub
          hF.aestronglyMeasurable).norm.pow 2)
    hbound
    (by
      intro m
      filter_upwards [] with q
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hzero := sourceRadialCutoff_nonneg m q
      have hone := sourceRadialCutoff_le_one m q
      have hscalar : |sourceRadialCutoff m q - 1| ≤ 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hone)]
        linarith
      have hrewrite :
          (sourceRadialCutoff m q : ℂ) • F q - F q =
            ((sourceRadialCutoff m q - 1 : ℝ) : ℂ) • F q := by
        simp [sub_smul]
      rw [hrewrite, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      apply (sq_le_sq₀
        (mul_nonneg (abs_nonneg _) (norm_nonneg _))
        (norm_nonneg _)).mpr
      simpa using mul_le_mul_of_nonneg_right hscalar
        (norm_nonneg (F q)))
    (by
      filter_upwards [] with q
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [sourceRadialCutoff_eventually_one q]
        with m hm
      simp [hm])
  simpa using hdom
end Ehrhart.TorusFriedrichsCutoff
