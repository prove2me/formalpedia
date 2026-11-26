-- Prove2me | solution 1 for ClassicalComplexWPT.exactOrder_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:18.074071+00:00
-- url     : https://prove2.me/submissions/c79c95b2-a6ee-4e7e-ae42-a4e095a2aac4

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
theorem _root_.solution (n d : ℕ) :
    ExactOrderInLastVariable (fun x : Ambient n ↦ x.2 ^ d) d := by
  constructor
  · intro k hk
    change iteratedDeriv k (fun w : ℂ ↦ w ^ d) 0 = 0
    simpa [ne_of_lt hk] using
      (iteratedDeriv_fun_pow_zero (𝕜 := ℂ) (n := k) (m := d))
  · change iteratedDeriv d (fun w : ℂ ↦ w ^ d) 0 ≠ 0
    simp
end ClassicalComplexWPT
