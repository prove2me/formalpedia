-- Prove2me | solution 1 for ClassicalComplexWPT.isWeierstrassPreparation_nonconstantUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:15.671088+00:00
-- url     : https://prove2.me/submissions/0c496ad1-7844-4219-8528-274609371f64

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
    IsWeierstrassPreparation
      (fun x : Ambient 1 ↦ (1 + x.2) * (x.2 + x.1 0)) 1
      (fun _ z ↦ z 0) (fun x ↦ 1 + x.2) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ rfl, ?_, by simp, ?_⟩
  · let pr : Base 1 →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)
    exact pr.analyticAt 0
  · exact analyticAt_const.add analyticAt_snd
  · filter_upwards
    simp [preparedPolynomial]
end ClassicalComplexWPT
