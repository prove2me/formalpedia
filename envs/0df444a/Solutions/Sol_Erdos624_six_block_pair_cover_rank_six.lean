-- Prove2me | solution 1 for Erdos624.six_block_pair_cover_rank_six
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:50.905713+00:00
-- url     : https://prove2.me/submissions/590dfec8-b8f3-4ad5-a71a-6e44a846fcb5

import Mathlib
open Finset

namespace E624R14X
open Finset

theorem six : (∀ i : Fin 6, #((![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i) = 5) ∧
    (∀ x y : Fin 10, ∃ i : Fin 6,
      x ∉ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i ∧
      y ∉ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i) ∧
    (∀ c : Fin 6 → ZMod 2, (∀ x : Fin 10, ∑ i : Fin 6, c i *
      (if x ∈ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i then 1 else 0) = 0) → c = 0) := by
  decide
end E624R14X

namespace Erdos624

theorem six_block_pair_cover_rank_six : (∀ i : Fin 6, #((![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i) = 5) ∧
    (∀ x y : Fin 10, ∃ i : Fin 6,
      x ∉ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i ∧
      y ∉ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i) ∧
    (∀ c : Fin 6 → ZMod 2, (∀ x : Fin 10, ∑ i : Fin 6, c i *
      (if x ∈ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i then 1 else 0) = 0) → c = 0) := by
  exact E624R14X.six

end Erdos624

open Finset

theorem solution : (∀ i : Fin 6, #((![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i) = 5) ∧
    (∀ x y : Fin 10, ∃ i : Fin 6,
      x ∉ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i ∧
      y ∉ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i) ∧
    (∀ c : Fin 6 → ZMod 2, (∀ x : Fin 10, ∑ i : Fin 6, c i *
      (if x ∈ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i then 1 else 0) = 0) → c = 0) :=
  Erdos624.six_block_pair_cover_rank_six 
