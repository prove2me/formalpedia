-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2_sub_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/1da30788-aa90-40b1-9eb2-fd8bb57d86f3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral
import Theorems.Thm_Ehrhart_TorusStrongWeightedCutoffAdjoint_angularClosedMollifiedRadialAdjointCommutator_sub_weak

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousRadialAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert WeightedBrascampLieb
open WeightedResolventConstantCore MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault TorusMollifiedBochner
open TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator TorusWeakRadialExteriorMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusHomogeneousRadialAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ)
    {B : ℝ}
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B) :
    ‖angularClosedMollifiedRadialAdjointCommutatorL2
        ha W ℓ m -
      (angularWeakSourceCutoffAdjointCommutator_memLp
        W hB m).toLp
        (angularWeakSourceCutoffAdjointCommutator W m)‖ ^ 2 ≤
      (((m : ℝ) + 1)⁻¹ * B) ^ 2 *
        (∫ q in tsupport (sourceCutoffBarGradient (n := n) m),
          ‖torusFormRepresentative
              (angularGraphMollifiedPhysicalField W ℓ) q - W q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) := by
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  let S : Set (LogTorus n) :=
    tsupport (sourceCutoffBarGradient (n := n) m)
  let V : LogSpace n → LogSpace n :=
    angularGraphMollifiedPhysicalField W ℓ
  let A : ℝ := ((m : ℝ) + 1)⁻¹ * B
  let M : angularWeightedScalarL2 a :=
    angularClosedMollifiedRadialAdjointCommutatorL2 ha W ℓ m
  let R : angularWeightedScalarL2 a :=
    (angularWeakSourceCutoffAdjointCommutator_memLp
      W hB m).toLp
        (angularWeakSourceCutoffAdjointCommutator W m)
  have hB₀ : 0 ≤ B :=
    (norm_nonneg
      (euclideanGradient (fun y : Space n => unitBump y)
        (0 : Space n))).trans
      (hB (0 : Space n))
  have hA : 0 ≤ A := mul_nonneg (by positivity) hB₀
  let : IsLocallyFiniteMeasure μ :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have hS : IsCompact S :=
    (sourceCutoffBarGradient_hasCompactSupport m).isCompact
  have hV : ContDiff ℝ 2 V :=
    WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2
  have hp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d) :=
    angularGraphMollifiedPhysicalField_periodic W ℓ
  have hVc : Continuous (torusFormRepresentative V) :=
    continuous_torusFormRepresentative_of_smooth_periodic hV hp
  have hVm : MemLp (torusFormRepresentative V) 2
      (μ.restrict S) := by
    apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (hVc.aestronglyMeasurable.mono_measure
        Measure.restrict_le_self)).mpr
    exact (hVc.norm.pow 2).continuousOn.integrableOn_compact hS
  have hWm : MemLp (fun q : LogTorus n => W q) 2
      (μ.restrict S) :=
    (MeasureTheory.Lp.memLp W).mono_measure
      Measure.restrict_le_self
  have hdiff : IntegrableOn
      (fun q : LogTorus n =>
        ‖torusFormRepresentative V q - W q‖ ^ 2) S μ :=
    (hVm.sub hWm).norm.integrable_sq
  have hMmem := angularClosedMollifiedRadialAdjointCommutator_memLp
    ha W ℓ m
  have hRmem := angularWeakSourceCutoffAdjointCommutator_memLp
    W hB m
  have hM :
      (fun q : LogTorus n => M q) =ᵐ[μ]
        angularSourceCutoffAdjointCommutator m V := by
    simpa [M, μ, V,
      angularClosedMollifiedRadialAdjointCommutatorL2]
      using hMmem.coeFn_toLp
  have hR :
      (fun q : LogTorus n => R q) =ᵐ[μ]
        angularWeakSourceCutoffAdjointCommutator W m := by
    simpa [R, μ] using hRmem.coeFn_toLp
  have hnorm :
      ‖M - R‖ ^ 2 =
        ∫ q : LogTorus n,
          ‖angularSourceCutoffAdjointCommutator m V q -
            angularWeakSourceCutoffAdjointCommutator W m q‖ ^ 2
          ∂μ := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Lp.coeFn_sub M R, hM, hR]
      with q hsub hm hr
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hm, hr]
  have hleft : Integrable
      (fun q : LogTorus n =>
        ‖angularSourceCutoffAdjointCommutator m V q -
          angularWeakSourceCutoffAdjointCommutator W m q‖ ^ 2)
      μ :=
    (hMmem.sub hRmem).norm.integrable_sq
  have hright : Integrable
      (S.indicator
        (fun q : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2)) μ :=
    (MeasureTheory.integrable_indicator_iff hS.measurableSet).mpr
      (hdiff.const_mul (A ^ 2))
  have hpoint (q : LogTorus n) :
      ‖angularSourceCutoffAdjointCommutator m V q -
        angularWeakSourceCutoffAdjointCommutator W m q‖ ^ 2 ≤
      S.indicator
        (fun r : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q := by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      have hb :
          ‖angularSourceCutoffAdjointCommutator m V q -
            angularWeakSourceCutoffAdjointCommutator W m q‖ ≤
            A * ‖torusFormRepresentative V q - W q‖ := by
        change
          ‖angularSourceCutoffAdjointCommutator m
            (angularGraphMollifiedPhysicalField W ℓ) q -
            angularWeakSourceCutoffAdjointCommutator W m q‖ ≤
            A * ‖torusFormRepresentative V q - W q‖
        rw [TorusStrongWeightedCutoffAdjoint.angularClosedMollifiedRadialAdjointCommutator_sub_weak]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right
            (sourceCutoffBarGradient_norm_le hB m q)
            (norm_nonneg _))
      calc
        _ ≤ (A * ‖torusFormRepresentative V q - W q‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg hA (norm_nonneg _))).mpr hb
        _ = _ := by rw [mul_pow]
    · rw [Set.indicator_of_notMem hq]
      have hz : sourceCutoffBarGradient m q = 0 :=
        image_eq_zero_of_notMem_tsupport hq
      change
        ‖angularSourceCutoffAdjointCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q -
          angularWeakSourceCutoffAdjointCommutator W m q‖ ^ 2 ≤ 0
      rw [TorusStrongWeightedCutoffAdjoint.angularClosedMollifiedRadialAdjointCommutator_sub_weak,
        hz]
      simp
  change ‖M - R‖ ^ 2 ≤
    A ^ 2 *
      (∫ q in S,
        ‖torusFormRepresentative V q - W q‖ ^ 2 ∂μ)
  rw [hnorm]
  calc
    _ ≤ ∫ q : LogTorus n,
      S.indicator
        (fun r : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q
      ∂μ := integral_mono hleft hright hpoint
    _ = ∫ q in S,
      A ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2
      ∂μ := MeasureTheory.integral_indicator hS.measurableSet
    _ = _ := integral_const_mul (A ^ 2) _
end Ehrhart.TorusHomogeneousRadialAdjoint
