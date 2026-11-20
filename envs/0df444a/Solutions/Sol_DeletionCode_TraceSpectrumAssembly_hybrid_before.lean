-- Prove2me | solution 1 for DeletionCode.TraceSpectrumAssembly.hybrid_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:49:03.705113+00:00
-- url     : https://prove2.me/submissions/b0a9b9f8-cd53-4288-a3b5-94d9e2f14817

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_append


set_option autoImplicit true
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators
namespace DeletionCode.TraceSpectrumAssembly
theorem _root_.solution (trace : Trace) (i : Fin trace.length) :
    hybrid trace i.val = Trace.target (trace.take i.val) ++
      (Trace.source [trace.get i] ++ Trace.source (trace.drop (i.val + 1))) := by
  unfold hybrid
  have hdrop : trace.drop i.val = trace.get i :: trace.drop (i.val + 1) :=
    List.drop_eq_getElem_cons i.isLt
  rw [hdrop]
  congr 1
  exact Trace.source_append [trace.get i] (trace.drop (i.val + 1))
end DeletionCode.TraceSpectrumAssembly
