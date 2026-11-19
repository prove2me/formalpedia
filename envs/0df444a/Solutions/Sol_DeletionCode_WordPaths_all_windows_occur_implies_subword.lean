-- Prove2me | solution 1 for DeletionCode.WordPaths.all_windows_occur_implies_subword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:59:30.829026+00:00
-- url     : https://prove2.me/submissions/13347e36-5dce-4504-8fc4-8fec69a37603

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_WordPaths
import Theorems.Thm_DeletionCode_WordPaths_consecutive_occurrences

set_option autoImplicit true
open DeletionCode DeletionCode.WordPaths
open Windows
namespace DeletionCode.WordPaths
theorem _root_.solution
    (x p : Letters) (n k L D : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (hocc : ∀ i, i ≤ D → Occurs x n p i L) :
    ∃ a, a + (L + D) ≤ n ∧ Agree x a p 0 (L + D) := by
  obtain ⟨a, ha, hzero⟩ := hocc 0 (by omega)
  have aligned : ∀ i, i ≤ D →
      a + i + L ≤ n ∧ Agree x (a + i) p i L := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro ha hzero
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨b, hb, hnext⟩ := hocc (i + 1) hi
      have heq := consecutive_occurrences x p n k L i (a + i) b
        hx hk hprev.1 hb hprev.2 hnext
      constructor
      · omega
      · have hindex : a + (i + 1) = b := by omega
        simpa only [hindex] using hnext
  refine ⟨a, by have hlast := (aligned D le_rfl).1; omega, ?_⟩
  intro j hj
  let i := min j D
  have hiD : i ≤ D := Nat.min_le_right j D
  have hij : i ≤ j := Nat.min_le_left j D
  have hlocal : j - i < L := by
    dsimp [i]
    by_cases h : j ≤ D
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have heq := (aligned i hiD).2 (j - i) hlocal
  have hsource : a + i + (j - i) = a + j := by omega
  have htarget : i + (j - i) = 0 + j := by omega
  simpa only [hsource, htarget] using heq
end DeletionCode.WordPaths
