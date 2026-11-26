-- Prove2me | solution 1 for ClassicalComplexWPT.exactOrder_pow_add_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:06.271285+00:00
-- url     : https://prove2.me/submissions/ed71220c-60ff-456b-af07-4ecdd0e5717c

import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_ClassicalComplexWPT_Examples
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_preparedPolynomial_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.preparedPolynomial_zero



set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) :
    ExactOrderInLastVariable (fun x : Ambient 1 ↦ x.2 ^ d + x.1 0) d := by
  constructor
  · intro k hk
    change iteratedDeriv k (fun w : ℂ ↦ w ^ d + (0 : Base 1) 0) 0 = 0
    simpa [ne_of_lt hk] using
      (iteratedDeriv_fun_pow_zero (𝕜 := ℂ) (n := k) (m := d))
  · change iteratedDeriv d (fun w : ℂ ↦ w ^ d + (0 : Base 1) 0) 0 ≠ 0
    simp
end ClassicalComplexWPT
