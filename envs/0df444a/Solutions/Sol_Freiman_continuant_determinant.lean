-- Prove2me | solution 1 for Freiman.continuant_determinant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:26:52.566757+00:00
-- url     : https://prove2.me/submissions/d7a76c1d-5884-4de0-ac2c-0cb34dd8582b

import Definitions.Def_Freiman_continuants
import Theorems.Thm_Freiman_continuant_append

open Freiman

theorem solution (w : List ℕ+) :
    (wordContinuantPrevP w : ℤ) * wordContinuantQ w -
      (wordContinuantP w : ℤ) * wordContinuantPrevQ w = (-1 : ℤ) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => norm_num [wordContinuantPrevP, wordContinuantP, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
  | append_singleton w a ih =>
    have h := continuant_append w a
    simp only [wordContinuantPrevP, wordContinuantP, wordContinuantPrevQ, wordContinuantQ] at *
    rw [h]
    simp only [List.length_append, List.length_singleton, pow_succ]
    push_cast
    nlinarith
