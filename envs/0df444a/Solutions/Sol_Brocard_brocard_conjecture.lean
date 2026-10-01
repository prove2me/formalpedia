-- Prove2me | solution 1 for Brocard.brocard_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-01T00:52:50.804492+00:00
-- url     : https://prove2.me/submissions/4036d167-fe2a-493b-b37b-7898dc3f32cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Brocard_brocard_conjecture_of_lt_100
import Theorems.Thm_Brocard_brocard_conjecture_of_ge_100
open Finset Filter

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card := by
  rcases Nat.lt_or_ge n 100 with h | h
  · exact Brocard.brocard_conjecture_of_lt_100 n hn h
  · exact Brocard.brocard_conjecture_of_ge_100 n h
