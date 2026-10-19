-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousSmoothRootBochner.angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/6b21844d-8015-4ae3-b862-fb44913209e2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusNoncompactBochner_angularTorus_compact_form_curvature_le_adjoint_add_exterior
import Theorems.Thm_Ehrhart_TorusHomogeneousSmoothRootBochner_angularSmoothCompactHessianRootVector_L2_norm_sq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousSmoothRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph
open RadialPhysicalInverseSquareRootEnergy TorusRootCurvatureCoercivity TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusMollifiedBochner TorusWeakRadialExteriorEnergy
open TorusClosedMollifiedRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusHomogeneousSmoothRootBochner
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → LogSpace n)
    (hV : ContDiff ℝ 2 V)
    (hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d))
    (m : ℕ) :
    ‖(angularSmoothCompactHessianRootVector_memLp
      ha ha2 hH V hV hVp m).toLp
        (angularSmoothCompactHessianRootVector a V m)‖ ^ 2 ≤
    (∫ q : LogTorus n,
      angularTorusFormAdjoint a (cutoffPhysicalField m V) q *
      conj (angularTorusFormAdjoint a
        (cutoffPhysicalField m V) q)
      ∂(angularWeightedTorusMeasure a)).re +
    (∫ q : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re := by
  rw [angularSmoothCompactHessianRootVector_L2_norm_sq
    ha ha2 hH V hV hVp m]
  exact angularTorus_compact_form_curvature_le_adjoint_add_exterior
    (cutoffPhysicalField m V) ha ha2
    (fun i => contDiff_pi.mp (contDiff_cutoffPhysicalField m hV) i)
    (fun i d z => congrFun
      (cutoffPhysicalField_periodic m hVp d z) i)
    (cutoffPhysicalField_coordinate_hasCompactSupport m V)
end Ehrhart.TorusHomogeneousSmoothRootBochner
