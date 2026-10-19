-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.iUnion_binaryAngularFundamentalBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/9fa80699-cd8a-4daa-b282-cc1d1b0f74d8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    (n : ℕ) :
    (⋃ q : Fin n → Bool,
      angularFundamentalBox (binaryAngularFundamentalBase q)) =
      Set.univ.pi (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp ht
    intro i _
    have hi := hq i
    change
      t i ∈ Set.Ioc
        (if q i then (-1 : ℝ) else 0)
        ((if q i then (-1 : ℝ) else 0) + 1) at hi
    change (-1 : ℝ) < t i ∧ t i ≤ 1
    cases hqi : q i
    · simp [hqi] at hi
      exact ⟨by linarith [hi.1], hi.2⟩
    · simp [hqi] at hi
      exact ⟨hi.1, by linarith [hi.2]⟩
  · intro ht
    let q : Fin n → Bool := fun i => decide (t i ≤ 0)
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    intro i
    have hi := ht i (Set.mem_univ i)
    change
      t i ∈ Set.Ioc
        (if q i then (-1 : ℝ) else 0)
        ((if q i then (-1 : ℝ) else 0) + 1)
    by_cases hzero : t i ≤ 0
    · have hq : q i = true := by
        simp [q, hzero]
      rw [hq]
      simpa using
        (show (-1 : ℝ) < t i ∧ t i ≤ 0 from ⟨hi.1, hzero⟩)
    · have hq : q i = false := by
        simp [q, hzero]
      rw [hq]
      simpa using
        (show 0 < t i ∧ t i ≤ (1 : ℝ) from
          ⟨lt_of_not_ge hzero, hi.2⟩)
end Ehrhart.MatrixTorusBochnerBridge
