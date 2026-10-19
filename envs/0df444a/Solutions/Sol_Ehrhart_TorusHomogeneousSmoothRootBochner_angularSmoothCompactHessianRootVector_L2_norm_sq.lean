-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousSmoothRootBochner.angularSmoothCompactHessianRootVector_L2_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/7f8c6f68-5720-4748-b946-026280f80169

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusFormCurvatureDensity
import Theorems.Thm_Ehrhart_TorusHomogeneousSmoothRootBochner_angularCurvatureDensity_re_eq_squareRoot_norm_sq

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
        (angularSmoothCompactHessianRootVector a V m)‖ ^ 2 =
    (∫ q : LogTorus n,
      angularTorusFormCurvatureDensity a
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re := by
  have hcurv : Integrable
      (angularTorusFormCurvatureDensity a
        (cutoffPhysicalField m V))
      (angularWeightedTorusMeasure a) :=
    integrable_angularTorusFormCurvatureDensity
      (cutoffPhysicalField m V) ha ha2
      (fun i => contDiff_pi.mp
        (contDiff_cutoffPhysicalField m hV) i)
      (fun i d z => congrFun
        (cutoffPhysicalField_periodic m hVp d z) i)
      (cutoffPhysicalField_coordinate_hasCompactSupport m V)
  rw [complexLp_norm_sq_eq_integral]
  change
    (∫ q : LogTorus n,
      ‖(angularSmoothCompactHessianRootVector_memLp
        ha ha2 hH V hV hVp m).toLp
          (angularSmoothCompactHessianRootVector a V m) q‖ ^ 2
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      angularTorusFormCurvatureDensity a
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re
  calc
    (∫ q : LogTorus n,
      ‖(angularSmoothCompactHessianRootVector_memLp
        ha ha2 hH V hV hVp m).toLp
          (angularSmoothCompactHessianRootVector a V m) q‖ ^ 2
      ∂(angularWeightedTorusMeasure a)) =
      ∫ q : LogTorus n,
        (angularTorusFormCurvatureDensity a
          (cutoffPhysicalField m V) q).re
        ∂(angularWeightedTorusMeasure a) := by
          apply integral_congr_ae
          filter_upwards
            [(angularSmoothCompactHessianRootVector_memLp
              ha ha2 hH V hV hVp m).coeFn_toLp]
            with q hq
          rw [hq]
          exact
            (angularCurvatureDensity_re_eq_squareRoot_norm_sq
              hH (cutoffPhysicalField m V) q).symm
    _ = (∫ q : LogTorus n,
      angularTorusFormCurvatureDensity a
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re := by
        simpa using (integral_re hcurv)
end Ehrhart.TorusHomogeneousSmoothRootBochner
