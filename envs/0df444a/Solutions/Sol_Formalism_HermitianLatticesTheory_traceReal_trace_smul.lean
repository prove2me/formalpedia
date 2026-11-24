-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.traceReal_trace_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:00.905372+00:00
-- url     : https://prove2.me/submissions/dce9d75f-639a-47a5-8741-3473d4365652

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Definitions.Def_Lemmata_GeneralBFactSecondSide_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (q : ℚ) (z : K) :
    Algebra.trace ℚ K (algebraMap ℚ K q * z) = q * Algebra.trace ℚ K z := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]
end Formalism.HermitianLatticesTheory
