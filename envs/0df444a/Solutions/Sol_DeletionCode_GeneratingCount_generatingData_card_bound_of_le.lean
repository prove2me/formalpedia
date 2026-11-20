-- Prove2me | solution 1 for DeletionCode.GeneratingCount.generatingData_card_bound_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:22.545055+00:00
-- url     : https://prove2.me/submissions/9cd63caf-ba83-4782-a509-8ae1f8a03ee7

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
import Theorems.Thm_DeletionCode_GeneratingCount_generatingData_card_le_description
import Theorems.Thm_DeletionCode_DescriptionCount_description_bound


set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount
namespace DeletionCode.GeneratingCount
theorem _root_.solution (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) (hc : c ≤ ν) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  exact (generatingData_card_le_description x n k ν c hν hx).trans
    (description_bound n (windowLength k) ν c (by unfold windowLength; omega) hν hc)
end DeletionCode.GeneratingCount
