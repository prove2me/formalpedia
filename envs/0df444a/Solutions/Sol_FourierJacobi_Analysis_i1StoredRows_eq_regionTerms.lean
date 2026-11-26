-- Prove2me | solution 1 for FourierJacobi.Analysis.i1StoredRows_eq_regionTerms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:29:20.49663+00:00
-- url     : https://prove2.me/submissions/b06141a7-66bc-4fda-b197-bdbf09e247b2

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ) (i : Fin 15) :
    i1StoredRows t d U V T i =
      regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by
  fin_cases i <;> rfl
end FourierJacobi.Analysis
