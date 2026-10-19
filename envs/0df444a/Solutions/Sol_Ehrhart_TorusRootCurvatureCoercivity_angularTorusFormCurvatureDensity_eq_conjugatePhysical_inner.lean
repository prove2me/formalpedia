-- Prove2me | solution 1 for Ehrhart.TorusRootCurvatureCoercivity.angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/0271f454-073b-4aba-8650-b1603e139636

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusRootCurvatureCoercivity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert ComplexKillingSaturationBridge WeightedTorusBochner
open WeightedTorusBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusRootCurvatureCoercivity
theorem _root_.solution
    {n : ℕ} (a : LogTorus n → ℝ)
    (W : LogSpace n → Fin n → ℂ) (q : LogTorus n) :
    angularTorusFormCurvatureDensity a W q =
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (angularTorusConjugatePhysicalFormVector W q)
        (Matrix.toEuclideanLin
          (angularTorusComplexHessianMatrix a q)
          (angularTorusConjugatePhysicalFormVector W q)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [angularTorusFormCurvatureDensity,
    angularTorusConjugatePhysicalFormVector,
    angularTorusComplexHessianMatrix, dotProduct,
    Matrix.mulVec, Pi.star_apply,
    Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
end Ehrhart.TorusRootCurvatureCoercivity
