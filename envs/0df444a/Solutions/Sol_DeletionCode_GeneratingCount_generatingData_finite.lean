-- Prove2me | solution 1 for DeletionCode.GeneratingCount.generatingData_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:06.348102+00:00
-- url     : https://prove2.me/submissions/a31d91e9-5c3a-4196-a71b-4280d414435e

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
    Finite {data : RecoveredData ν // GeneratingData x n k ν c data} :=
  Finite.of_injective (encodeGeneratingData x n k ν c hν hx)
    (encodeGeneratingData_injective x n k ν c hν hx)
end DeletionCode.GeneratingCount
