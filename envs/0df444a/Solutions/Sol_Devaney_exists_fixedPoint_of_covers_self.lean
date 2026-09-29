-- Prove2me | solution 1 for Devaney.exists_fixedPoint_of_covers_self
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T21:08:09.596896+00:00
-- url     : https://prove2.me/submissions/dbfd7e27-73b8-45a9-a598-8d49d13e4449

import Mathlib
import Definitions.Def_Devaney_sarkovskii

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DevFix

open Devaney

/-- §1.10, first observation: a continuous map whose image of `[a,b]` covers `[a,b]` has a
fixed point there. -/
theorem exists_fixedPoint_of_covers_self (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ)
    (hab : a ≤ b) (h : Covers f (Set.Icc a b) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = x := by
  obtain ⟨p, hp, hpa⟩ := h (Set.left_mem_Icc.2 hab)
  obtain ⟨q, hq, hqb⟩ := h (Set.right_mem_Icc.2 hab)
  set g : ℝ → ℝ := fun x => f x - x with hg
  have hgc : ContinuousOn g (Set.uIcc p q) := (hf.sub continuous_id).continuousOn
  have hgp : g p ≤ 0 := by simp only [hg, hpa]; linarith [hp.1]
  have hgq : 0 ≤ g q := by simp only [hg, hqb]; linarith [hq.2]
  have hmem : (0 : ℝ) ∈ Set.uIcc (g p) (g q) := Set.mem_uIcc.2 (Or.inl ⟨hgp, hgq⟩)
  obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hgc hmem
  refine ⟨x, ?_, by simpa [hg, sub_eq_zero] using hx0⟩
  have hsub : Set.uIcc p q ⊆ Set.Icc a b := Set.uIcc_subset_Icc hp hq
  exact hsub hx

end DevFix

open Devaney in
theorem solution (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ)
    (hab : a ≤ b) (h : Covers f (Set.Icc a b) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = x :=
  DevFix.exists_fixedPoint_of_covers_self f hf a b hab h
