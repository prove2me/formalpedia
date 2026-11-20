-- Prove2me | solution 1 for DeletionCode.GeneratingCount.generatingData_card_le_description
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:07.052182+00:00
-- url     : https://prove2.me/submissions/fae583ac-7ad0-40f4-99d8-dbfe77c655e7

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
import Theorems.Thm_DeletionCode_GeneratingCount_encodeGeneratingData_injective

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount
namespace DeletionCode.GeneratingCount
theorem _root_.solution (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      Fintype.card (Description n (windowLength k) ν c) := by
  simpa only [Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_injective (encodeGeneratingData x n k ν c hν hx)
      (encodeGeneratingData_injective x n k ν c hν hx)
end DeletionCode.GeneratingCount
