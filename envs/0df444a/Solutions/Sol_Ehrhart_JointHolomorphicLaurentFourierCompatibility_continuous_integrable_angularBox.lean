-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.continuous_integrable_angularBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/1c6ffad2-3602-4343-a32d-e4a7be224fe4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularBoxMeasure_eq_restrict

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
theorem _root_.solution {n : ℕ}
    {g : Space n → ℂ} (hg : Continuous g) :
    Integrable g (angularBoxMeasure n) := by
  rw [angularBoxMeasure_eq_restrict]
  apply (hg.integrableOn_Icc (a := (0 : Space n))
    (b := (1 : Space n))).mono_set
  intro x hx
  change (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1)
  constructor
  · intro i
    exact (hx i (Set.mem_univ i)).1.le
  · intro i
    exact (hx i (Set.mem_univ i)).2
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
