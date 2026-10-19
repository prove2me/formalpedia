-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousSmoothRootBochner.angularCurvatureDensity_re_eq_squareRoot_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/9cdaf8a1-903b-4ba3-9609-e311030ab9e4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusDolbeaultGraph_angularMatrixSquareRoot_posDef
import Theorems.Thm_Ehrhart_TorusRootCurvatureCoercivity_angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner

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
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → Fin n → ℂ) (q : LogTorus n) :
    (angularTorusFormCurvatureDensity a V q).re =
      ‖Matrix.toEuclideanLin
        (angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q)
        (angularTorusConjugatePhysicalFormVector V q)‖ ^ 2 := by
  rw [angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner]
  rw [complexHermitianMatrixAction_norm_sq
    (angularMatrixSquareRoot_posDef hH q).isHermitian]
  rw [show
    angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q *
      angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q =
        angularTorusComplexHessianMatrix a q from
      CFC.sqrt_mul_sqrt_self _ (hH q).posSemidef.nonneg]
  rfl
end Ehrhart.TorusHomogeneousSmoothRootBochner
