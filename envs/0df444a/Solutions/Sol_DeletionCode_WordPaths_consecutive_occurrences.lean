-- Prove2me | solution 1 for DeletionCode.WordPaths.consecutive_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:59:06.728201+00:00
-- url     : https://prove2.me/submissions/d931656d-dc26-4512-a99d-395955fb5f30

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_WordPaths

set_option autoImplicit true
open DeletionCode DeletionCode.WordPaths
open Windows
namespace DeletionCode.WordPaths
theorem _root_.solution
    (x p : Letters) (n k L i a b : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hleft : Agree x a p i L) (hright : Agree x b p (i + 1) L) :
    b = a + 1 := by
  have hmatch : Agree x (a + 1) x b k := by
    intro j hj
    have hl := hleft (j + 1) (by omega)
    have hr := hright j (by omega)
    calc
      x (a + 1 + j) = x (a + (j + 1)) := congrArg x (by omega)
      _ = p (i + (j + 1)) := hl
      _ = p (i + 1 + j) := congrArg p (by omega)
      _ = x (b + j) := hr.symm
  exact (hx (a + 1) b (by omega) (by omega) hmatch).symm
end DeletionCode.WordPaths
