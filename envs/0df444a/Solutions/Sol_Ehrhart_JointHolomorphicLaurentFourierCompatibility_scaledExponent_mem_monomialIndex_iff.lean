-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.scaledExponent_mem_monomialIndex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/60216f71-7471-4708-8a34-146cf6d3ee7d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_integerPoint_eq_smul_scaledExponent

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
    (hk : 0 < k) (m : Fin n → ℤ) :
    scaledExponent k m ∈
        LatticeAsymptotics.monomialIndex K k ↔
      scaledExponent k m ∈ interior K.carrier := by
  rw [LatticeAsymptotics.mem_monomialIndex_iff K hk]
  constructor
  · exact And.left
  · intro hmem
    refine ⟨hmem, ?_⟩
    intro i
    refine ⟨m i, ?_⟩
    have h :=
      congrFun (integerPoint_eq_smul_scaledExponent hk m) i
    simpa [integerPoint] using h
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
