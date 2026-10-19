-- Prove2me | solution 1 for Ehrhart.TorusWeakResolventRootBochner.angularEuclideanConjugation_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/57f06b28-78c8-4ac5-b79d-8af8a7f5d481

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
    {n : ℕ} (v w : EuclideanSpace ℂ (Fin n)) :
    angularEuclideanConjugation (v - w) =
      angularEuclideanConjugation v -
        angularEuclideanConjugation w := by
  ext i
  change conj (v i - w i) = conj (v i) - conj (w i)
  exact map_sub (starRingEnd ℂ) (v i) (w i)
end Ehrhart.TorusWeakResolventRootBochner
