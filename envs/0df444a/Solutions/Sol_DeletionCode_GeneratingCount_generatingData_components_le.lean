-- Prove2me | solution 1 for DeletionCode.GeneratingCount.generatingData_components_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:14:25.19812+00:00
-- url     : https://prove2.me/submissions/023df34a-f423-412a-bc02-c9cb0dc1607b

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
import Theorems.Thm_DeletionCode_GeneratingCount_editedFamily_component_count_le

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount
namespace DeletionCode.GeneratingCount
theorem _root_.solution (x : Letters) (n k ν c : ℕ)
    (data : RecoveredData ν) (hdata : GeneratingData x n k ν c data) : c ≤ ν := by
  obtain ⟨E, _, hc, _⟩ := hdata
  rw [← hc]
  exact editedFamily_component_count_le E
end DeletionCode.GeneratingCount
