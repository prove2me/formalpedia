-- Prove2me | solution 1 for ClassicalComplexWPT.exactOrder_nonconstantUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:24.107184+00:00
-- url     : https://prove2.me/submissions/c5d0382c-48d1-42c6-beee-ecd0dfc8c6a2

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
theorem _root_.solution :
    ExactOrderInLastVariable
      (fun x : Ambient 1 ↦ (1 + x.2) * (x.2 + x.1 0)) 1 := by
  constructor
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp [lastSlice]
  · unfold lastSlice
    simp only [Pi.zero_apply, add_zero]
    rw [iteratedDeriv_succ']
    simp only [iteratedDeriv_zero]
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    norm_num
end ClassicalComplexWPT
