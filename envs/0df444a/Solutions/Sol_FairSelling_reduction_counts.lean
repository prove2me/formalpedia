-- Prove2me | solution 1 for FairSelling.reduction_counts
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:24:01.493798+00:00
-- url     : https://prove2.me/submissions/bcd2ae56-e84b-42b1-8dbf-29722a79ac53

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsReduction
set_option autoImplicit true
open FairSelling


theorem solution {L n0 n2 : ℕ} (hlow : n0 + 1 < L) (hhigh : L < 2 * n0)
    (hcard : L ≤ n0 + n2 + 1) :
    (L - n0 - 1 ≤ n2) ∧ L - 2 * (L - n0 - 1) = (n0 - (L - n0 - 1)) + 1 := by
  omega
