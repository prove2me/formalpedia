-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularClosedMollifiedRootVectorL2_sub_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/3097391d-0bc4-47a8-b42b-f43f5a37ad9a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularClosedMollifiedRootVector_sub_pointwise

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open JetEnvelopeRightDerivative EqualitySaturatingKillingPaths ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerCoreDensity
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusWeightedAdjointMollification TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy TorusWeakRadialBochnerUpperBound
open TorusWeakRadialExteriorMollification TorusClosedMollifiedRootBochner
open TorusStrongWeightedCutoffAdjoint TorusWeakResolventRootBochner
open RadialPhysicalResolventRootCutoffUniformExtraction TorusHomogeneousSmoothRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ q ∈ tsupport (sourceRadialCutoff (n := n) m),
      ∀ v : EuclideanSpace ℂ (Fin n),
        ‖Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q) v‖ ≤ B * ‖v‖) :
    ‖angularClosedMollifiedRootVectorL2
        ha ha2 hH W ℓ m -
      angularPhysicalResolventRootCutoffL2
        ha2 hH W m‖ ^ 2 ≤
      B ^ 2 *
        (∫ q in tsupport (sourceRadialCutoff (n := n) m),
          ‖torusFormRepresentative
              (angularGraphMollifiedPhysicalField W ℓ) q - W q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) := by
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  let S : Set (LogTorus n) :=
    tsupport (sourceRadialCutoff (n := n) m)
  let V : LogSpace n → LogSpace n :=
    angularGraphMollifiedPhysicalField W ℓ
  let U : angularWeightedFormL2 a :=
    angularClosedMollifiedRootVectorL2 ha ha2 hH W ℓ m
  let R : angularWeightedFormL2 a :=
    angularPhysicalResolventRootCutoffL2 ha2 hH W m
  let : IsLocallyFiniteMeasure μ :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have hS : IsCompact S :=
    (sourceRadialCutoff_hasCompactSupport m).isCompact
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
  have hsmooth := angularSmoothCompactHessianRootVector_memLp
    ha ha2 hH V hV hp m
  have hweak := angularPhysicalResolventRootCutoffField_memLp
    ha2 hH W m
  have hU :
      (fun q : LogTorus n => U q) =ᵐ[μ]
        angularSmoothCompactHessianRootVector a V m := by
    simpa [U, V, μ, angularClosedMollifiedRootVectorL2]
      using hsmooth.coeFn_toLp
  have hR :
      (fun q : LogTorus n => R q) =ᵐ[μ]
        angularPhysicalResolventRootCutoffField a W m := by
    simpa [R, μ, angularPhysicalResolventRootCutoffL2]
      using hweak.coeFn_toLp
  have hroot :
      ‖U - R‖ ^ 2 =
        ∫ q : LogTorus n,
          ‖angularSmoothCompactHessianRootVector a V m q -
            angularPhysicalResolventRootCutoffField a W m q‖ ^ 2 ∂μ := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Lp.coeFn_sub U R, hU, hR]
      with q hsub hu hr
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hu, hr]
  have hleft : Integrable
      (fun q : LogTorus n =>
        ‖angularSmoothCompactHessianRootVector a V m q -
          angularPhysicalResolventRootCutoffField a W m q‖ ^ 2) μ :=
    (hsmooth.sub hweak).norm.integrable_sq
  have hright : Integrable
      (S.indicator
        (fun q : LogTorus n =>
          B ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2)) μ :=
    (MeasureTheory.integrable_indicator_iff hS.measurableSet).mpr
      (hdiff.const_mul (B ^ 2))
  have hpoint (q : LogTorus n) :
      ‖angularSmoothCompactHessianRootVector a V m q -
        angularPhysicalResolventRootCutoffField a W m q‖ ^ 2 ≤
        S.indicator
          (fun r : LogTorus n =>
            B ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q := by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      have he := angularClosedMollifiedRootVector_sub_pointwise
        W ℓ m q
      have hnorm :
          ‖angularSmoothCompactHessianRootVector a V m q -
            angularPhysicalResolventRootCutoffField a W m q‖ ≤
          B * ‖torusFormRepresentative V q - W q‖ := by
        rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
        calc
          sourceRadialCutoff m q *
              ‖Matrix.toEuclideanLin
                (angularMatrixSquareRoot
                  (angularTorusComplexHessianMatrix a) q)
                (angularEuclideanConjugation
                  (torusFormRepresentative V q - W q))‖ ≤
            ‖Matrix.toEuclideanLin
                (angularMatrixSquareRoot
                  (angularTorusComplexHessianMatrix a) q)
                (angularEuclideanConjugation
                  (torusFormRepresentative V q - W q))‖ :=
              mul_le_of_le_one_left (norm_nonneg _)
                (sourceRadialCutoff_le_one m q)
          _ ≤ B * ‖angularEuclideanConjugation
              (torusFormRepresentative V q - W q)‖ :=
            hB q hq _
          _ = B * ‖torusFormRepresentative V q - W q‖ := by
            rw [norm_angularEuclideanConjugation]
      calc
        _ ≤ (B * ‖torusFormRepresentative V q - W q‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg hB₀ (norm_nonneg _))).mpr hnorm
        _ = _ := by rw [mul_pow]
    · rw [Set.indicator_of_notMem hq]
      have hz : sourceRadialCutoff m q = 0 :=
        image_eq_zero_of_notMem_tsupport hq
      have he := angularClosedMollifiedRootVector_sub_pointwise
        W ℓ m q
      rw [he, hz]
      simp
  change ‖U - R‖ ^ 2 ≤
    B ^ 2 *
      (∫ q in S, ‖torusFormRepresentative V q - W q‖ ^ 2 ∂μ)
  rw [hroot]
  calc
    _ ≤ ∫ q : LogTorus n,
      S.indicator
        (fun r : LogTorus n =>
          B ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q
        ∂μ := integral_mono hleft hright hpoint
    _ = ∫ q in S,
      B ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2
        ∂μ := MeasureTheory.integral_indicator hS.measurableSet
    _ = _ := integral_const_mul (B ^ 2) _
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
