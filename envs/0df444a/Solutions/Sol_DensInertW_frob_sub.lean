-- Prove2me | solution 1 for DensInertW.frob_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:53.61781+00:00
-- url     : https://prove2.me/submissions/075e9dff-ca20-420c-86b5-24a93bf8742b

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
theorem _root_.solution (x y : L) :
    (x - y) ^ Fintype.card K = x ^ Fintype.card K - y ^ Fintype.card K :=
  map_sub (conj K) x y
end DensInertW
