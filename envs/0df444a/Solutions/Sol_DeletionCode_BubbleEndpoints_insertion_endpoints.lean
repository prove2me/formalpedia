-- Prove2me | solution 1 for DeletionCode.BubbleEndpoints.insertion_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:51.356071+00:00
-- url     : https://prove2.me/submissions/f0f05a1f-b856-4311-a46c-5cb35af020e2

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
import Theorems.Thm_DeletionCode_BubbleEndpoints_endpoints_of_displacement
import Theorems.Thm_DeletionCode_BubbleEndpoints_insertion_window_displacement
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_longWord_length
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_shortWord_length

section
namespace DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
private theorem local_window_bounds {k : ℕ} (bubble : BubbleWord k) (a b : ℕ)
    (ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho) :
    a + (windowLength k - 1) ≤ bubble.longWord.length ∧
      b + (windowLength k - 1) ≤ bubble.shortWord.length := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, longLength, shortLength,
    BubbleWord.header]
  unfold windowLength at *
  omega
private theorem transfer_equal_windows (p q x y : Letters) (s a b m lenp lenq : ℕ)
    (hp : Agree p 0 x s lenp) (hq : Agree q 0 y s lenq)
    (ha : a + m ≤ lenp) (hb : b + m ≤ lenq) (hag : Agree p a q b m) :
    Agree x (s + a) y (s + b) m := by
  intro i hi
  calc
    x (s + a + i) = p (a + i) := by
      simpa only [Nat.zero_add, Nat.add_assoc] using (hp (a + i) (by omega)).symm
    _ = q (b + i) := hag i hi
    _ = y (s + b + i) := by
      simpa only [Nat.zero_add, Nat.add_assoc] using hq (b + i) (by omega)
end DeletionCode.BubbleEndpoints
end

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubbleEndpoints
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit))
    (x : Letters) (hx : KUnique x n k) (pos : ℕ) (bit : Bool) (hpos : pos ≤ n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n + 1)
    (hslength : s + bubble.shortWord.length ≤ n)
    (hlong : Agree (listLetters bubble.longWord) 0 (insertAt x pos bit) s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 x s bubble.shortWord.length)
    (a b : ℕ) (ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.shortWord) b (windowLength k - 1)) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho) := by
  obtain ⟨halocal, hblocal⟩ := local_window_bounds bubble a b ha hb
  have hglobal := transfer_equal_windows _ _ _ _ s a b _ _ _ hlong hshort halocal hblocal hag
  exact endpoints_of_displacement bubble hleft hright a b ha hb hag
    (insertion_window_displacement hk x hx pos bit hpos s a b (by omega) (by omega) hglobal)
end DeletionCode.BubbleEndpoints
