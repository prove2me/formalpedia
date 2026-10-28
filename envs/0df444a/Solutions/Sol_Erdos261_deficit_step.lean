-- Prove2me | solution 1 for Erdos261.deficit_step
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:27:51.862586+00:00
-- url     : https://prove2.me/submissions/a61a6e5f-dd1f-41fb-8123-335ea1b6afb6

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset


namespace E261R4
open Erdos261

theorem deficit_step (n j : ℕ) (h : ((n + j + 1 : ℕ) : ℤ) ≤ 2 * greedy n j) :
    ((n + j + 1 : ℕ) : ℤ) - greedy n (j + 1) = 2 * (((n + j : ℕ) : ℤ) - greedy n j) + 2 := by
  rw [greedy, if_pos h]; push_cast; ring

theorem S_block (n j ℓ : ℕ)
    (h : ∀ i < ℓ, ((n + j + i + 1 : ℕ) : ℤ) ≤ 2 * greedy n (j + i)) :
    greedy n (j + ℓ) + 2 ^ ℓ * ((((n + j : ℕ) : ℤ) - greedy n j) + 2) = ((n + j + ℓ : ℕ) : ℤ) + 2 := by
  induction ℓ with
  | zero => simp; ring
  | succ l ih =>
    have ih' := ih (fun i hi => h i (by omega))
    have hs := h l (by omega)
    have e : greedy n (j + (l + 1)) = 2 * greedy n (j + l) - ((n + j + l + 1 : ℕ) : ℤ) := by
      rw [show j + (l + 1) = (j + l) + 1 by omega, greedy, if_pos (by
        rw [show n + (j + l) + 1 = n + j + l + 1 by omega]; exact hs)]
      push_cast; ring
    rw [e, pow_succ]; push_cast at ih' ⊢; linear_combination 2 * ih'

theorem D_block (n j t : ℕ)
    (h : ∀ i < t, 2 * greedy n (j + i) < ((n + j + i + 1 : ℕ) : ℤ)) :
    greedy n (j + t) = 2 ^ t * greedy n j := by
  induction t with
  | zero => simp
  | succ l ih =>
    have ih' := ih (fun i hi => h i (by omega))
    have hs := h l (by omega)
    rw [show j + (l + 1) = (j + l) + 1 by omega, greedy, if_neg (by
      rw [show n + (j + l) + 1 = n + j + l + 1 by omega]; exact not_le.2 hs), ih', pow_succ]
    ring

end E261R4


namespace Erdos261

theorem deficit_step (n j : ℕ) (h : ((n + j + 1 : ℕ) : ℤ) ≤ 2 * greedy n j) :
    ((n + j + 1 : ℕ) : ℤ) - greedy n (j + 1) = 2 * (((n + j : ℕ) : ℤ) - greedy n j) + 2 :=
  E261R4.deficit_step n j h

end Erdos261

open Erdos261 in
theorem solution (n j : ℕ) (h : ((n + j + 1 : ℕ) : ℤ) ≤ 2 * greedy n j) :
    ((n + j + 1 : ℕ) : ℤ) - greedy n (j + 1) = 2 * (((n + j : ℕ) : ℤ) - greedy n j) + 2 :=
  Erdos261.deficit_step n j h

#print axioms solution
