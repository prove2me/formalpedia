-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.integerExponent_eq_of_integerPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/11c12701-a692-40dc-99df-65d2a01128d1

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
    (u : LatticeAsymptotics.monomialIndex K k)
    (m : Fin n → ℤ)
    (hm : integerPoint n m =
      (k : ℝ) • (u : Space n)) :
    WeightedTorusHilbert.integerExponent K hk u = m := by
  have hreal :
      integerPoint n
        (WeightedTorusHilbert.integerExponent K hk u) =
      integerPoint n m :=
    (WeightedTorusHilbert.integerPoint_integerExponent
      K hk u).trans hm.symm
  funext i
  have hi := congrFun hreal i
  change ((WeightedTorusHilbert.integerExponent
    K hk u i : ℤ) : ℝ) = ((m i : ℤ) : ℝ) at hi
  exact_mod_cast hi
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
