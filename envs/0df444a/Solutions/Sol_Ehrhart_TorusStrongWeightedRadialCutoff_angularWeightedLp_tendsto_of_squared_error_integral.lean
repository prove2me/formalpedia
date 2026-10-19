-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedRadialCutoff.angularWeightedLp_tendsto_of_squared_error_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/21df8970-aee9-406a-bda6-c116700124eb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongWeightedRadialCutoff
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongWeightedRadialCutoff
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {F : ℕ → LogTorus n → E} {f : LogTorus n → E}
    (hF : ∀ k : ℕ, MemLp (F k) 2 (angularWeightedTorusMeasure a))
    (hf : MemLp f 2 (angularWeightedTorusMeasure a))
    (hconv : Tendsto
      (fun k : ℕ =>
        ∫ q : LogTorus n, ‖F k q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ => (hF k).toLp (F k))
      atTop (nhds (hf.toLp f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq (k : ℕ) :
      ‖(hF k).toLp (F k) - hf.toLp f‖ ^ 2 =
        ∫ q : LogTorus n, ‖F k q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a) := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards
      [MeasureTheory.Lp.coeFn_sub
        ((hF k).toLp (F k)) (hf.toLp f),
       (hF k).coeFn_toLp, hf.coeFn_toLp]
      with q hsub hleft hright
    rw [hsub]
    change
      ‖((hF k).toLp (F k)) q - (hf.toLp f) q‖ ^ 2 = _
    rw [hleft, hright]
  have hsqtendsto :
      Tendsto
        (fun k : ℕ => ‖(hF k).toLp (F k) - hf.toLp f‖ ^ 2)
        atTop (nhds 0) := by
    simpa only [hsq] using hconv
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    hsqtendsto
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hsqrt
end Ehrhart.TorusStrongWeightedRadialCutoff
