-- Prove2me | solution 1 for Freiman.continuant_reverse
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:45:05.407416+00:00
-- url     : https://prove2.me/submissions/460dea75-53bf-4aa1-bde8-10a4f814f64e

import Definitions.Def_Freiman_continuants
import Theorems.Thm_Freiman_continuant_denominator_pos
import Mathlib.Tactic.FieldSimp

open Freiman

set_option autoImplicit false

private theorem reverse_word (w : List ℕ+) :
    finiteCF w.reverse = (wordContinuantPrevQ w : ℝ) / wordContinuantQ w := by
  induction w using List.reverseRecOn with
  | nil => simp [wordContinuantPrevQ, wordContinuantQ, wordContinuantData, finiteCF]
  | append_singleton w a ih =>
    have hq : (wordContinuantQ w : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast continuant_denominator_pos w)
    have step : wordContinuantData (w ++ [a]) =
        ((wordContinuantP w, (a : ℕ) * wordContinuantP w + wordContinuantPrevP w),
         (wordContinuantQ w, (a : ℕ) * wordContinuantQ w + wordContinuantPrevQ w)) := by
      simp [wordContinuantData, List.foldl_append, wordContinuantP,
        wordContinuantQ, wordContinuantPrevP, wordContinuantPrevQ]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, finiteCF, ih]
    simp only [wordContinuantPrevQ, wordContinuantQ, step, Nat.cast_add, Nat.cast_mul]
    change 1 / (((a : ℕ) : ℝ) + (wordContinuantPrevQ w : ℝ) / wordContinuantQ w) =
      (wordContinuantQ w : ℝ) /
        (((a : ℕ) : ℝ) * wordContinuantQ w + wordContinuantPrevQ w)
    field_simp [hq]

theorem solution (b : ℕ → ℕ+) (n : ℕ) :
    finiteCF (((List.range n).map b).reverse) =
      (continuantPrevQ b n : ℝ) / continuantQ b n := by
  exact reverse_word ((List.range n).map b)
