-- Prove2me | solution 1 for DeletionCode.GeneratingCount.generatingData_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:47.445138+00:00
-- url     : https://prove2.me/submissions/299d3640-3fb9-46e3-afe1-7914438f4b4b

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
import Theorems.Thm_DeletionCode_GeneratingCount_generatingData_components_le
import Theorems.Thm_DeletionCode_GeneratingCount_generatingData_card_bound_of_le

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount
namespace DeletionCode.GeneratingCount
theorem _root_.solution (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  by_cases hc : c ≤ ν
  · exact generatingData_card_bound_of_le x n k ν c hν hx hc
  · let : IsEmpty {data : RecoveredData ν // GeneratingData x n k ν c data} :=
      ⟨fun data => hc (generatingData_components_le x n k ν c data.val data.property)⟩
    simp
end DeletionCode.GeneratingCount
