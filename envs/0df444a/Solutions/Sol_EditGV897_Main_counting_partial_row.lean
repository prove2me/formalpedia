-- Prove2me | solution 1 for EditGV897.Main.counting_partial_row
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:48:49.997415+00:00
-- url     : https://prove2.me/submissions/ef13b06d-a988-41ac-8d9d-706e182a5004

import Theorems.Thm_EditGV897_Main_partial_row_semantics
import Theorems.Thm_EditGV897_Main_partial_row_programs

open EditGV897.Main

theorem solution :
    ∃ (counter evaluator rowBuilder : Program) (A d : ℕ), 0 < A ∧
      (∀ (n : ℕ) (E : List (Equation n)),
        affineCount E = (affineSet E).card ∧
        Runs counter (unary n ++ equationCode E) (binary (affineCount E))
          (polyBudget A d (n + E.length))) ∧
      (∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length ≤ n →
        (∀ E : List (Equation n), witnessCount F G E = witnessSum F G (affineSet E)) ∧
        (∀ p : List Bit, p.length ≤ n →
          (twiceExpectation F G p : ℚ) = 2 * expectation F G p ∧
          Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
            (polyBudget A d (n + F.length))) ∧
        2 * witnessSum F (G ++ [chooseRow F G]) Finset.univ ≤ witnessSum F G Finset.univ ∧
        Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
          (polyBudget A d (n + F.length))) := by
  obtain ⟨counter, evaluator, rowBuilder, A, d, hA, hc, hr⟩ := partial_row_programs
  refine ⟨counter, evaluator, rowBuilder, A, d, hA, ?_, ?_⟩
  · intro n E
    exact ⟨partial_row_semantics.1 n E, hc n E⟩
  · intro n t F G ht hF hG
    obtain ⟨hw, he, hh⟩ := partial_row_semantics.2 n t F G ht hF hG
    obtain ⟨hev, hrow⟩ := hr n t F G ht hF hG
    exact ⟨hw, fun p hp => ⟨he p hp, hev p hp⟩, hh, hrow⟩
