-- Prove2me | solution 1 for Ehrhart.TorusWeightedCoverGlobalGreen.barPartialCoordinate_finset_sum_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/074431f3-6a48-4080-9abd-fc155ed2ace4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedCoverGlobalGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
namespace Ehrhart.TorusWeightedCoverGlobalGreen
theorem _root_.solution
    {n : ℕ} {ι : Type*} (s : Finset ι)
    (ψ : ι → LogSpace n → ℂ)
    (hψ : ∀ i ∈ s, ContDiff ℝ 1 (ψ i))
    (j : Fin n) (z : LogSpace n) :
    barPartialCoordinate (fun w => ∑ i ∈ s, ψ i w) z j =
      ∑ i ∈ s, barPartialCoordinate (ψ i) z j := by
  unfold barPartialCoordinate
  rw [fderiv_fun_sum
    (fun i hi => (hψ i hi).differentiable (by simp) z)]
  simp [Finset.mul_sum, Finset.sum_mul,
    div_eq_mul_inv, ← Finset.sum_add_distrib]
end Ehrhart.TorusWeightedCoverGlobalGreen
