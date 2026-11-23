-- Prove2me | solution 1 for DensInertW.frob_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:40:01.144349+00:00
-- url     : https://prove2.me/submissions/ef392f4d-d17b-4613-baba-e7d27fedb76f

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
    (x + y) ^ Fintype.card K = x ^ Fintype.card K + y ^ Fintype.card K :=
  map_add (conj K) x y
end DensInertW
