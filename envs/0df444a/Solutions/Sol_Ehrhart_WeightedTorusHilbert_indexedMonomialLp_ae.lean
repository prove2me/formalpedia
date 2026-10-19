-- Prove2me | solution 1 for Ehrhart.WeightedTorusHilbert.indexedMonomialLp_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/fad6b439-347d-417a-8f16-53152e323d60

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Set MeasureTheory Filter
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
open Ehrhart.WeightedTorusHilbert
attribute [local instance] Ehrhart.WeightedTorusHilbert._p2m_local_instance_3610026555_1046
attribute [local instance] Ehrhart.WeightedTorusHilbert._p2m_local_instance_3610026555_1049
namespace Ehrhart.WeightedTorusHilbert
theorem _root_.solution {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (u : LatticeAsymptotics.monomialIndex K k) :
    (indexedMonomialLp K hk hφ hbounded u : LogTorus n → ℂ)
      =ᵐ[weightedTorusMeasure k φ]
        torusMonomial (integerExponent K hk u) := by
  unfold indexedMonomialLp
  exact MeasureTheory.MemLp.coeFn_toLp _
end Ehrhart.WeightedTorusHilbert
