-- Prove2me | solution 1 for Freiman.continuant_fibonacci
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:04.176529+00:00
-- url     : https://prove2.me/submissions/75f39e39-3802-47ba-b083-b64d9e507b07

import Definitions.Def_Freiman_continuants
import Theorems.Thm_Freiman_continuant_fibonacci_pair

open Freiman

theorem solution (w : List ℕ+) :
    Nat.fib (w.length + 1) ≤ wordContinuantQ w := by
  exact (continuant_fibonacci_pair w).2
