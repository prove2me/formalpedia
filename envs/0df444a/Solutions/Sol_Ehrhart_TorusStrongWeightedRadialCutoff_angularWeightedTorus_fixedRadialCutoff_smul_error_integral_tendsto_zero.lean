-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedRadialCutoff.angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/c4351b95-21de-45a4-a01d-7a2f5468413d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℕ → LogTorus n → E}
    {f : LogTorus n → E}
    (hlocal : ∀ (k : ℕ) {S : Set (LogTorus n)}, IsCompact S →
      IntegrableOn
        (fun q : LogTorus n => ‖F k q - f q‖ ^ 2)
        S (angularWeightedTorusMeasure a))
    (hconv : ∀ {S : Set (LogTorus n)}, IsCompact S →
      Tendsto
        (fun k : ℕ =>
          ∫ q in S, ‖F k q - f q‖ ^ 2
            ∂(angularWeightedTorusMeasure a))
        atTop (nhds 0))
    (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) • F k q -
            (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  classical
  let S : Set (LogTorus n) :=
    tsupport (sourceRadialCutoff (n := n) m)
  have hS : IsCompact S :=
    sourceRadialCutoff_hasCompactSupport m
  have hpoint (k : ℕ) (q : LogTorus n) :
      ‖(sourceRadialCutoff m q : ℂ) • F k q -
          (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2 ≤
        S.indicator
          (fun p : LogTorus n => ‖F k p - f p‖ ^ 2) q := by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      have hscalar : ‖(sourceRadialCutoff m q : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
        exact sourceRadialCutoff_le_one m q
      have hnorm :
          ‖(sourceRadialCutoff m q : ℂ) • F k q -
            (sourceRadialCutoff m q : ℂ) • f q‖ ≤
          ‖F k q - f q‖ := by
        rw [← smul_sub, norm_smul]
        calc
          ‖(sourceRadialCutoff m q : ℂ)‖ * ‖F k q - f q‖ ≤
              1 * ‖F k q - f q‖ :=
            mul_le_mul_of_nonneg_right hscalar
              (norm_nonneg _)
          _ = _ := one_mul _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
    · have hzero : sourceRadialCutoff m q = 0 :=
        image_eq_zero_of_notMem_tsupport hq
      simp [Set.indicator_of_notMem hq, hzero]
  have hbound (k : ℕ) :
      (∫ q : LogTorus n,
        ‖(sourceRadialCutoff m q : ℂ) • F k q -
          (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) ≤
      ∫ q in S, ‖F k q - f q‖ ^ 2
        ∂(angularWeightedTorusMeasure a) := by
    calc
      _ ≤ ∫ q : LogTorus n,
        S.indicator
          (fun p : LogTorus n => ‖F k p - f p‖ ^ 2) q
          ∂(angularWeightedTorusMeasure a) := by
        apply MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall
            (fun q => sq_nonneg _))
          ((hlocal k hS).integrable_indicator hS.measurableSet)
        exact Filter.Eventually.of_forall (hpoint k)
      _ = _ := MeasureTheory.integral_indicator hS.measurableSet
  exact squeeze_zero
    (fun k => integral_nonneg (fun q => sq_nonneg _))
    hbound
    (hconv hS)
end Ehrhart.TorusStrongWeightedRadialCutoff
