-- Prove2me | solution 2 for EditGV897.Main.encoding_recovering_messages
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:30:00.235194+00:00
-- url     : https://prove2.me/submissions/2c44a3a9-2905-495e-b7b6-6e5b0ff5c867

import Theorems.Thm_EditGV897_Main_affine_count_correct
import Theorems.Thm_EditGV897_Main_witness_count_correct
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
  obtain ⟨encoder, inverter, A, d, hA, hr⟩ := encoding_programs
  refine ⟨encoder, inverter, A, d, hA, ?_⟩
  intro n t F P ht hF hlen hlt hrank hβ hroot
  have hs := signed_code_indexing F P hF hβ (affine_count_correct n)
    (witness_count_correct n F P.rows) hroot
  refine ⟨hs.1, ?_⟩
  intro u
  have hu := hs.2 u
  have hruns := hr n t F P ht hF hlen hlt hrank hβ hroot u
  exact ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1,
    hu.2.2.2.2.2, hruns.1, hruns.2⟩
