-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.generating_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:25.883664+00:00
-- url     : https://prove2.me/submissions/cc7cfb11-f6c2-41fc-bad2-c0139c5f2ff1

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
import Theorems.Thm_DeletionCode_WitnessAlgebra_span_support
import Theorems.Thm_DeletionCode_WitnessAlgebra_negative_step_source

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {H : Type*} (v p q : H → ℚ) (S : Set (H → ℚ))
    (hp : BooleanVector p) (hq : BooleanVector q)
    (hspan : p - v ∈ Submodule.span ℚ S) (h : H)
    (hneg : (q - p) h = -1) : v h ≠ 0 ∨ ∃ w ∈ S, w h ≠ 0 := by
  classical
  by_cases hv : v h = 0
  · right
    apply span_support S (p - v) hspan h
    have hpone := negative_step_source p q hp hq h hneg
    simp [hpone, hv]
  · exact Or.inl hv
end DeletionCode.WitnessAlgebra
