-- Prove2me | solution 1 for ClassicalComplexWPT.isWeierstrassPreparation_pow_add_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:09.40841+00:00
-- url     : https://prove2.me/submissions/395b4d6d-4eae-4b2d-8571-f4b5f4f6148a

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
theorem _root_.solution (d : ℕ) (hd : 0 < d) :
    IsWeierstrassPreparation (fun x : Ambient 1 ↦ x.2 ^ d + x.1 0) d
      (fun i z ↦ if (i : ℕ) = 0 then z 0 else 0) (fun _ ↦ 1) := by
  classical
  refine ⟨?_, ?_, analyticAt_const, one_ne_zero, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) = 0
    · simp only [hi, if_true]
      let pr : Base 1 →L[ℂ] ℂ :=
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)
      exact pr.analyticAt 0
    · simp only [hi, if_false]
      exact analyticAt_const
  · intro i
    simp
  · filter_upwards with x
    simp only [one_mul]
    unfold preparedPolynomial
    rw [Finset.sum_eq_single ⟨0, hd⟩]
    · simp
    · intro b _ hb
      have hb0 : (b : ℕ) ≠ 0 := by
        intro h
        apply hb
        apply Fin.ext
        simpa using h
      simp [hb0]
    · simp
end ClassicalComplexWPT
