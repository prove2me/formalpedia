-- Prove2me | solution 2 for FairSelling.reduction_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:44.53011+00:00
-- url     : https://prove2.me/submissions/2f602269-c045-429e-8003-00b107bfcd9e

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsReduction

set_option autoImplicit true
open FairSelling
namespace FairSelling
theorem _root_.solution {L n0 n2 : ℕ} (hlow : n0 + 1 < L) (hhigh : L < 2 * n0)
    (hcard : L ≤ n0 + n2 + 1) :
    (L - n0 - 1 ≤ n2) ∧ L - 2 * (L - n0 - 1) = (n0 - (L - n0 - 1)) + 1 := by
  omega
end FairSelling
