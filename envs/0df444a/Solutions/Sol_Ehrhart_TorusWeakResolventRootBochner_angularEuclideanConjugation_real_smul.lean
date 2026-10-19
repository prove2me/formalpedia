-- Prove2me | solution 1 for Ehrhart.TorusWeakResolventRootBochner.angularEuclideanConjugation_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/aeb5fd4a-7b9a-441e-92d7-189b4aa58e14

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeakResolventRootBochner
open Set Function Filter MeasureTheory Matrix
open RadialPhysicalResolventRootCutoffPairing
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusWeakResolventRootBochner
theorem _root_.solution
    {n : ℕ} (c : ℝ) (v : EuclideanSpace ℂ (Fin n)) :
    angularEuclideanConjugation ((c : ℂ) • v) =
      (c : ℂ) • angularEuclideanConjugation v := by
  ext i
  change conj ((c : ℂ) * v i) = (c : ℂ) * conj (v i)
  simp
end Ehrhart.TorusWeakResolventRootBochner
