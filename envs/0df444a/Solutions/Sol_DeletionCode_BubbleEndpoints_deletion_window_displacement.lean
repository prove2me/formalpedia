-- Prove2me | solution 1 for DeletionCode.BubbleEndpoints.deletion_window_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:59.20454+00:00
-- url     : https://prove2.me/submissions/8f81c175-6944-4e6e-b8b1-1a943f894f82

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
import Theorems.Thm_DeletionCode_EditRigidity_shared_source_letters


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubbleEndpoints
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s a b : ℕ)
    (ha : s + a + (windowLength k - 1) ≤ n)
    (hb : s + b + (windowLength k - 1) ≤ n - 1)
    (hag : Agree x (s + a) (deleteAt x pos) (s + b) (windowLength k - 1)) :
    a = b ∨ a = b + 1 := by
  obtain ⟨r, u, _, _, hsource⟩ := EditRigidity.shared_source_letters hk x hx
    .unchanged (.delete pos) trivial hpos (s + a) (s + b) ha hb hag
  have hfirst := (hsource 0 (by omega)).1
  have hsecond := (hsource 0 (by omega)).2
  simp only [Edit.origin, Nat.add_zero, Option.some.injEq] at hfirst
  by_cases hcut : s + b + r < pos
  · simp only [Edit.origin, Nat.add_zero, if_pos hcut, Option.some.injEq] at hsecond
    exact Or.inl (by omega)
  · simp only [Edit.origin, Nat.add_zero, if_neg hcut, Option.some.injEq] at hsecond
    exact Or.inr (by omega)
end DeletionCode.BubbleEndpoints
