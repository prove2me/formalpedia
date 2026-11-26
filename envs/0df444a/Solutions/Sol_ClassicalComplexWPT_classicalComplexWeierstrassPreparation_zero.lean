-- Prove2me | solution 1 for ClassicalComplexWPT.classicalComplexWeierstrassPreparation_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:09.893243+00:00
-- url     : https://prove2.me/submissions/e0ffef79-958b-467e-9894-9161fc2ec88d

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Theorems.Thm_ClassicalComplexWPT_preparedPolynomial_zero
import Theorems.Thm_ClassicalComplexWPT_exactOrderInLastVariable_zero_iff
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastSlice_zero


attribute [local simp] ClassicalComplexWPT.preparedPolynomial_zero

set_option autoImplicit true
open Filter
open scoped Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution
    {n : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f 0) :
    ∃ (a : Fin 0 → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f 0 a u ∧
      ∀ (a' : Fin 0 → Base n → ℂ) (u' : Ambient n → ℂ),
        IsWeierstrassPreparation f 0 a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by
  refine ⟨fun i ↦ Fin.elim0 i, f, ?_, ?_⟩
  · refine ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, hf, ?_, ?_⟩
    · exact exactOrderInLastVariable_zero_iff.mp horder
    · filter_upwards
      simp
  · intro a' u' hu'
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    simpa using hu'.2.2.2.2
end ClassicalComplexWPT
