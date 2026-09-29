-- Prove2me | solution 1 for Freiman.continuant_denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:26:52.560188+00:00
-- url     : https://prove2.me/submissions/4377b9c9-d46c-4c48-9ef3-bf50f0156a90

import Definitions.Def_Freiman_continuants
import Theorems.Thm_Freiman_continuant_append

open Freiman

theorem solution (w : List ℕ+) :
    0 < wordContinuantQ w := by
  induction w using List.reverseRecOn with
  | nil => norm_num [wordContinuantQ, wordContinuantData]
  | append_singleton w a ih =>
    have hq : wordContinuantQ (w ++ [a]) = (a:ℕ)*wordContinuantQ w+wordContinuantPrevQ w :=
      congrArg (fun d : (ℕ×ℕ)×(ℕ×ℕ) => d.2.2) (continuant_append w a)
    rw [hq]
    exact Nat.add_pos_left (Nat.mul_pos a.pos ih) _
