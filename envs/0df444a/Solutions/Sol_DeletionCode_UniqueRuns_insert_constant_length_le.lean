-- Prove2me | solution 1 for DeletionCode.UniqueRuns.insert_constant_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:19.168168+00:00
-- url     : https://prove2.me/submissions/105683d5-812b-4153-8443-99f3c2991e84

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_UniqueRuns
import Theorems.Thm_DeletionCode_UniqueRuns_constant_length_le

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueRuns
open Windows
namespace DeletionCode.UniqueRuns
theorem _root_.solution (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (pos : ℕ) (insertedBit : Bool) (hpos : pos ≤ n)
    (a len : ℕ) (bit : Bool) (hbound : a + len ≤ n + 1)
    (hconstant : ConstantOn (insertAt x pos insertedBit) a len bit) : len ≤ k + 1 := by
  by_cases hbefore : a + len ≤ pos
  · have hsource : ConstantOn x a len bit := by
      intro i hi
      have hcut : a + i < pos := by omega
      simpa only [insertAt, if_pos hcut] using hconstant i hi
    have h := constant_length_le k n x hx a len bit (by omega) hsource
    omega
  · by_cases hafter : pos < a
    · have hsource : ConstantOn x (a - 1) len bit := by
        intro i hi
        have hcut : ¬ a + i < pos := by omega
        have hne : a + i ≠ pos := by omega
        have hindex : a + i - 1 = a - 1 + i := by omega
        simpa only [insertAt, if_neg hcut, if_neg hne, hindex]
          using hconstant i hi
      have h := constant_length_le k n x hx (a - 1) len bit (by omega) hsource
      omega
    · have hsource : ConstantOn x a (len - 1) bit := by
        intro i hi
        by_cases hcut : a + i < pos
        · simpa only [insertAt, if_pos hcut] using hconstant i (by omega)
        · have hcutNext : ¬ a + (i + 1) < pos := by omega
          have hne : a + (i + 1) ≠ pos := by omega
          have hindex : a + (i + 1) - 1 = a + i := by omega
          simpa only [insertAt, if_neg hcutNext, if_neg hne, hindex]
            using hconstant (i + 1) (by omega)
      have h := constant_length_le k n x hx a (len - 1) bit (by omega) hsource
      omega
end DeletionCode.UniqueRuns
