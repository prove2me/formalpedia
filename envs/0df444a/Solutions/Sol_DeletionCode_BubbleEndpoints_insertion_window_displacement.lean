-- Prove2me | solution 1 for DeletionCode.BubbleEndpoints.insertion_window_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:59.691635+00:00
-- url     : https://prove2.me/submissions/2e5533d9-67da-4dca-ad35-eca376b6578d

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
import Theorems.Thm_DeletionCode_EditRigidity_shared_source_letters


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubbleEndpoints
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (pos : ℕ) (bit : Bool) (hpos : pos ≤ n) (s a b : ℕ)
    (ha : s + a + (windowLength k - 1) ≤ n + 1)
    (hb : s + b + (windowLength k - 1) ≤ n)
    (hag : Agree (insertAt x pos bit) (s + a) x (s + b) (windowLength k - 1)) :
    a = b ∨ a = b + 1 := by
  obtain ⟨r, u, _, _, hsource⟩ := EditRigidity.shared_source_letters hk x hx
    (.insert pos bit) .unchanged hpos trivial (s + a) (s + b) ha hb hag
  have hfirst := (hsource 0 (by omega)).1
  have hsecond := (hsource 0 (by omega)).2
  simp only [Edit.origin, Nat.add_zero, Option.some.injEq] at hsecond
  by_cases hcut : s + a + r < pos
  · simp only [Edit.origin, Nat.add_zero, if_pos hcut, Option.some.injEq] at hfirst
    exact Or.inl (by omega)
  · by_cases heq : s + a + r = pos
    · simp only [Edit.origin, Nat.add_zero, if_neg hcut, if_pos heq, reduceCtorEq] at hfirst
    · simp only [Edit.origin, Nat.add_zero, if_neg hcut, if_neg heq, Option.some.injEq] at hfirst
      exact Or.inr (by omega)
end DeletionCode.BubbleEndpoints
