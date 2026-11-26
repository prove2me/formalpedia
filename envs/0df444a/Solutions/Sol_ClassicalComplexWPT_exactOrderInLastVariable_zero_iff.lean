-- Prove2me | solution 1 for ClassicalComplexWPT.exactOrderInLastVariable_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:20.95231+00:00
-- url     : https://prove2.me/submissions/a8ab74c8-26f1-4bcf-a0f5-a3275e69bbb6

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ} {f : Ambient n → ℂ} :
    ExactOrderInLastVariable f 0 ↔ f 0 ≠ 0 := by
  have hzero : (0 : Ambient n) = ((0 : Base n), 0) := by
    ext <;> simp
  constructor
  · intro h
    rw [hzero]
    simpa [lastSlice] using h.2
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk
      omega
    · rw [iteratedDeriv_zero]
      change f ((0 : Base n), 0) ≠ 0
      rw [← hzero]
      exact h
end ClassicalComplexWPT
