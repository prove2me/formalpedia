-- Prove2me | solution 1 for DeletionCode.GeneratingCount.decode_encodeGeneratingData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:14:21.313698+00:00
-- url     : https://prove2.me/submissions/4e7d7d4d-2be3-4cf9-8c76-bd0fd0205797

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount
namespace DeletionCode.GeneratingCount
theorem _root_.solution (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k)
    (data : {data : RecoveredData ν // GeneratingData x n k ν c data}) :
    decodeDescription x n k ν c hν (encodeGeneratingData x n k ν c hν hx data) = some data.val :=
  Classical.choose_spec (generatingData_record_exists x n k ν c hν hx data)
end DeletionCode.GeneratingCount
