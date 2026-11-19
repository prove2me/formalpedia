-- Prove2me | solution 1 for DeletionCode.UniqueRuns.constant_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:21:25.558055+00:00
-- url     : https://prove2.me/submissions/03bbb9f1-6400-4fff-8c4a-ac43ce2908b0

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_UniqueRuns

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueRuns
open Windows
namespace DeletionCode.UniqueRuns
theorem _root_.solution (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (a len : ℕ) (bit : Bool) (hbound : a + len ≤ n)
    (hconstant : ConstantOn x a len bit) : len ≤ k := by
  by_contra hnot
  have hlong : k < len := by omega
  have heq : a = a + 1 := hx a (a + 1) (by omega) (by omega) (by
    intro i hi
    have hfirst := hconstant i (by omega)
    have hsecond := hconstant (i + 1) (by omega)
    have hindex : (a + 1) + i = a + (i + 1) := by omega
    rw [hindex]
    exact hfirst.trans hsecond.symm)
  omega
end DeletionCode.UniqueRuns
