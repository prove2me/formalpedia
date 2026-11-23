-- Prove2me | solution 1 for DensInertW.frob_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:53.542801+00:00
-- url     : https://prove2.me/submissions/e5087424-0471-4dc2-808d-d3d04638d944

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
omit [Fintype L]
namespace DensInertW
theorem _root_.solution (a : K) :
    (algebraMap K L a) ^ Fintype.card K = algebraMap K L a := by
  rw [← map_pow, FiniteField.pow_card]
end DensInertW
