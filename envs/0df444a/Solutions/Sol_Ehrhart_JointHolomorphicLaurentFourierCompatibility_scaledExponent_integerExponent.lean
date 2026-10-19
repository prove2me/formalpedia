-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.scaledExponent_integerExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/a97dd2f3-3e24-4cc6-812d-eb5f217b2e8e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918
namespace Ehrhart.JointHolomorphicLaurentFourierCompatibility
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n)
    (hk : 0 < k)
    (u : LatticeAsymptotics.monomialIndex K k) :
    scaledExponent k
        (WeightedTorusHilbert.integerExponent K hk u) =
      (u : Space n) := by
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  unfold scaledExponent
  rw [WeightedTorusHilbert.integerPoint_integerExponent]
  rw [smul_smul]
  simp [hkreal]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
