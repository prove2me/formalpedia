-- Prove2me | solution 1 for DilatableEntropy.one_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:55:43.827829+00:00
-- url     : https://prove2.me/submissions/90e43624-683d-4532-8165-752731114bdf

import Mathlib
import Definitions.Def_DilatableEntropy_gamma

open DilatableEntropy in
theorem solution (P : DilatableEntropy.SeqDecisionProblem) : ∀ j : P.J, 1 ≤ DilatableEntropy.gamma P j := by
  have hfix : ∀ j, DilatableEntropy.gamma P j = 1 + Finset.univ.sup' Finset.univ_nonempty
      (fun a : P.A j => ∑ j' ∈ (DilatableEntropy.children P (some ⟨j, a⟩)).attach,
        DilatableEntropy.gamma P j'.1) := by
    intro j
    unfold DilatableEntropy.gamma
    rw [WellFounded.fix_eq]
  intro j
  refine P.wf.induction (C := fun j => 1 ≤ DilatableEntropy.gamma P j) j ?_
  intro j IH
  rw [hfix]
  have a0 : P.A j := Classical.arbitrary _
  have hs : 0 ≤ ∑ j' ∈ (DilatableEntropy.children P (some ⟨j, a0⟩)).attach,
      DilatableEntropy.gamma P j'.1 :=
    Finset.sum_nonneg (fun j' _ => le_trans zero_le_one
      (IH j'.1 ⟨a0, (Finset.mem_filter.1 j'.2).2⟩))
  have := le_trans hs (Finset.le_sup' (fun a : P.A j =>
      ∑ j' ∈ (DilatableEntropy.children P (some ⟨j, a⟩)).attach, DilatableEntropy.gamma P j'.1)
    (Finset.mem_univ a0))
  linarith
