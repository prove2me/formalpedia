-- Prove2me | solution 1 for ClassicalComplexWPT.isWeierstrassPreparation_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:07:59.029505+00:00
-- url     : https://prove2.me/submissions/1b032821-195b-4670-b7c0-d9cb060c3ce9

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
    IsWeierstrassPreparation (fun x : Ambient n ↦ x.2 ^ d) d
      (fun _ _ ↦ 0) (fun _ ↦ 1) := by
  refine ⟨fun _ ↦ analyticAt_const, fun _ ↦ rfl, analyticAt_const, one_ne_zero, ?_⟩
  filter_upwards
  simp [preparedPolynomial]
end ClassicalComplexWPT
