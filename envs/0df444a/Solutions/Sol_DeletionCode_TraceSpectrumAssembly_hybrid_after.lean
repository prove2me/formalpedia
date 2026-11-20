-- Prove2me | solution 1 for DeletionCode.TraceSpectrumAssembly.hybrid_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:49:08.053374+00:00
-- url     : https://prove2.me/submissions/c595eaf2-945e-43c2-afb0-e6a106360413

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_target_append


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators
namespace DeletionCode.TraceSpectrumAssembly
theorem _root_.solution (trace : Trace) (i : Fin trace.length) :
    hybrid trace (i.val + 1) =
      (Trace.target (trace.take i.val) ++ Trace.target [trace.get i]) ++
        Trace.source (trace.drop (i.val + 1)) := by
  unfold hybrid
  rw [List.take_succ_eq_append_getElem i.isLt, Trace.target_append]
  rfl
end DeletionCode.TraceSpectrumAssembly
