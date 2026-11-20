-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.ruleSpectrum_signed_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:46.568994+00:00
-- url     : https://prove2.me/submissions/65daebc5-368e-44eb-8721-2a3badbd148c

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
import Theorems.Thm_DeletionCode_SignedSupport_bubble_negative_value
import Theorems.Thm_DeletionCode_SignedSupport_bubble_positive_value
import Theorems.Thm_DeletionCode_SignedSupport_rule_support_iff
import Theorems.Thm_DeletionCode_SignedSupport_rule_value_at_gram


set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {B : Type*} (F : RootSelection.Family B) (L : ℕ)
    (H : SignedSupport.BubbleGeometry F L) (S : Finset B)
    (hdis : SignedSupport.VertexDisjointOn F L S) :
    SignedUnitVector (fun g => (SignedSupport.ruleSpectrum F L S g : ℚ)) := by
  classical
  intro g
  by_cases hzero : SignedSupport.ruleSpectrum F L S g = 0
  · exact Or.inr (Or.inl (by simp [hzero]))
  · obtain ⟨b, hb, side, hwindow⟩ :=
      (SignedSupport.rule_support_iff F L H S hdis g).mp hzero
    have hvalue := SignedSupport.rule_value_at_gram F L H S hdis b hb g ⟨side, hwindow⟩
    cases side with
    | false =>
      left
      change (SignedSupport.ruleSpectrum F L S g : ℚ) = -1
      rw [hvalue, SignedSupport.bubble_negative_value F L H b g hwindow]
      norm_num
    | true =>
      right; right
      change (SignedSupport.ruleSpectrum F L S g : ℚ) = 1
      rw [hvalue, SignedSupport.bubble_positive_value F L H b g hwindow]
      norm_num
end DeletionCode.WitnessAlgebra
