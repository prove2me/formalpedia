-- Prove2me | solution 1 for DilatableEntropy.one_le_weight
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:18:18.75896+00:00
-- url     : https://prove2.me/submissions/01d03ad1-2cb4-4c67-96c1-7621ff787bcd

import Mathlib
import Definitions.Def_DilatableEntropy_weight

open DilatableEntropy in
theorem solution (P : SeqDecisionProblem) : ∀ σ : Seq P, 1 ≤ weight P σ := by
  intro σ
  rcases σ with _ | ⟨j, a⟩
  · change 1 ≤ gammaRoot P - ∑ j' ∈ children P none, gamma P j'
    unfold gammaRoot
    linarith
  · change 1 ≤ gamma P j - ∑ j' ∈ children P (some ⟨j, a⟩), gamma P j'
    have hg : gamma P j = 1 + Finset.univ.sup' Finset.univ_nonempty
        (fun a : P.A j => ∑ j' ∈ children P (some ⟨j, a⟩), gamma P j') := by
      conv_lhs => unfold gamma; rw [WellFounded.fix_eq]
      congr 1
      refine Finset.sup'_congr _ rfl fun b _ => ?_
      exact Finset.sum_attach (children P (some ⟨j, b⟩)) (fun j' => gamma P j')
    have hle := Finset.le_sup' (fun a : P.A j => ∑ j' ∈ children P (some ⟨j, a⟩), gamma P j')
      (Finset.mem_univ a)
    rw [hg]
    linarith
