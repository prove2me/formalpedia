-- Prove2me | solution 1 for EditGV897.Main.encoding_recovering_messages
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:50:31.364359+00:00
-- url     : https://prove2.me/submissions/c7a24cbc-40b8-444f-8fbd-91c9d96b647f

import Theorems.Thm_EditGV897_Main_counting_partial_row
import Theorems.Thm_EditGV897_Main_signed_code_indexing
import Theorems.Thm_EditGV897_Main_encoding_programs

open EditGV897.Main

theorem solution :
    ∃ (encoder inverter : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (P : Parameters n),
        1 ≤ t → EditFamily t F → P.rows.length = checkRows F.length → P.rows.length < n →
        FullRowRank P.rows → P.beta.length = P.rows.length →
        (2 ^ messageLength P : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta) →
        Function.Injective (encodeWord F P) ∧
        (∀ u : Word (messageLength P),
          let x := encodeWord F P u
          encodeList F P u = wordList x ∧ (encodeList F P u).length = n ∧
          syndrome P.rows x = P.beta ∧ Separated t P.rows x ∧
          (encodeSteps F P n [] (messageIndex (wordList u))).2 = 0 ∧
          inverseList F P (wordList x) = wordList u ∧
          Runs encoder (encoderInput F P u) (wordCode x) (polyBudget A d (n + F.length)) ∧
          Runs inverter (inverseInput F P (wordList x)) (wordCode u)
            (polyBudget A d (n + F.length))) := by
  obtain ⟨_, _, _, _, _, _, hc, hf⟩ := counting_partial_row
  obtain ⟨encoder, inverter, A, d, hA, hr⟩ := encoding_programs
  refine ⟨encoder, inverter, A, d, hA, ?_⟩
  intro n t F P ht hF hlen hlt hrank hβ hroot
  have hs := signed_code_indexing F P hF hβ (fun E => (hc n E).1)
    (hf n t F P.rows ht hF (Nat.le_of_lt hlt)).1 hroot
  refine ⟨hs.1, ?_⟩
  intro u
  have hu := hs.2 u
  have hruns := hr n t F P ht hF hlen hlt hrank hβ hroot u
  exact ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1,
    hu.2.2.2.2.2, hruns.1, hruns.2⟩
