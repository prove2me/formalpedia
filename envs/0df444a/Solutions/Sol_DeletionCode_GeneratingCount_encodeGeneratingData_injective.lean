-- Prove2me | solution 1 for DeletionCode.GeneratingCount.encodeGeneratingData_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:37.092815+00:00
-- url     : https://prove2.me/submissions/1bd60865-ef13-43bc-8b53-8d97aa96850b

import Definitions.Def_DeletionCode_RecordSerialization
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_GeneratingCount
import Theorems.Thm_DeletionCode_GeneratingCount_decode_encodeGeneratingData

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingCount
open Windows HeaderRecovery GeneratingModel GeneratingRecovery RecordSerialization DescriptionCount
namespace DeletionCode.GeneratingCount
theorem _root_.solution (x : Letters) (n k ν c : ℕ)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Function.Injective (encodeGeneratingData x n k ν c hν hx) := by
  intro a b hab
  have ha := decode_encodeGeneratingData x n k ν c hν hx a
  have hb := decode_encodeGeneratingData x n k ν c hν hx b
  rw [hab] at ha
  exact Subtype.ext (Option.some.inj (ha.symm.trans hb))
end DeletionCode.GeneratingCount
