-- Prove2me | solution 1 for DeletionCode.BubblePathSimplicity.substring_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:26.490323+00:00
-- url     : https://prove2.me/submissions/b42d3901-faeb-44b9-8d27-85ab9f089527

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity

set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins
namespace DeletionCode.BubblePathSimplicity
theorem _root_.solution (full word : Letters) (n len r s : ℕ)
    (hfull : KUnique full n r) (hbound : s + len ≤ n)
    (hocc : Agree word 0 full s len) : KUnique word len r := by
  intro a b ha hb hag
  have heq : s + a = s + b := hfull (s + a) (s + b) (by omega) (by omega) (by
    intro i hi
    calc
      full (s + a + i) = word (a + i) := by
        simpa only [Nat.zero_add, Nat.add_assoc] using
          (hocc (a + i) (by omega)).symm
      _ = word (b + i) := hag i hi
      _ = full (s + b + i) := by
        simpa only [Nat.zero_add, Nat.add_assoc] using hocc (b + i) (by omega))
  omega
end DeletionCode.BubblePathSimplicity
