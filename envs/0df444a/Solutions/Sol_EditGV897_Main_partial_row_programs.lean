-- Prove2me | solution 1 for EditGV897.Main.partial_row_programs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:38:24.075037+00:00
-- url     : https://prove2.me/submissions/1e62a77a-c0b9-401a-a223-ee586be2152a

import Theorems.Thm_EditGV897_Main_affine_counter_program
import Theorems.Thm_EditGV897_Main_expectation_row_programs


namespace EditGV897.Main
 theorem Runs.mono {P : Program} {input output : List Bool} {s t : ℕ}
    (h : Runs P input output s) (hst : s ≤ t) : Runs P input output t := by
  obtain ⟨k, hk, c, hc, hhalt, hout⟩ := h
  exact ⟨k, hk.trans hst, c, hc, hhalt, hout⟩



 theorem polyBudget_mono_parameters (s : ℕ) {A B d e : ℕ} (hAB : A ≤ B) (hde : d ≤ e) :
    polyBudget A d s ≤ polyBudget B e s := by
  unfold polyBudget
  exact Nat.mul_le_mul hAB (Nat.pow_le_pow_right (by omega) hde)

 theorem partial_runtime_assembly :
    ∃ (counter evaluator rowBuilder : Program) (A d : ℕ), 0 < A ∧
      (∀ (n : ℕ) (E : List (Equation n)),
        Runs counter (unary n ++ equationCode E) (binary (affineCount E))
          (polyBudget A d (n + E.length))) ∧
      (∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length ≤ n →
        (∀ p : List Bit, p.length ≤ n →
          Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
            (polyBudget A d (n + F.length))) ∧
        Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
          (polyBudget A d (n + F.length))) := by
  obtain ⟨counter, Ac, dc, hc, hcounter⟩ := affine_counter_program
  obtain ⟨evaluator, rowBuilder, Ae, de, he, hrow⟩ := expectation_row_programs
  refine ⟨counter, evaluator, rowBuilder, Ac+Ae, dc+de, by omega, ?_, ?_⟩
  · intro n E
    exact (hcounter n E).mono (polyBudget_mono_parameters _ (by omega) (by omega))
  · intro n t F G ht hF hG
    obtain ⟨hev, hr⟩ := hrow n t F G ht hF hG
    exact ⟨fun p hp => (hev p hp).mono (polyBudget_mono_parameters _ (by omega) (by omega)),
      hr.mono (polyBudget_mono_parameters _ (by omega) (by omega))⟩

end EditGV897.Main

open EditGV897.Main

theorem solution :
    ∃ (counter evaluator rowBuilder : Program) (A d : ℕ), 0 < A ∧
      (∀ (n : ℕ) (E : List (Equation n)),
        Runs counter (unary n ++ equationCode E) (binary (affineCount E))
          (polyBudget A d (n + E.length))) ∧
      (∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length ≤ n →
        (∀ p : List Bit, p.length ≤ n →
          Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
            (polyBudget A d (n + F.length))) ∧
        Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
          (polyBudget A d (n + F.length))) := EditGV897.Main.partial_runtime_assembly