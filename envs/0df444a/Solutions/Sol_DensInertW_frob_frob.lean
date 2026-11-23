-- Prove2me | solution 1 for DensInertW.frob_frob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:37.949804+00:00
-- url     : https://prove2.me/submissions/e603d059-0d2b-49cd-80c4-745df2f0dedf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Theorems.Thm_DensInertW_card_L

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
namespace DensInertW
theorem _root_.solution (h2 : Module.finrank K L = 2) (x : L) :
    (x ^ Fintype.card K) ^ Fintype.card K = x := by
  rw [← pow_mul, ← sq, ← card_L h2, FiniteField.pow_card]
end DensInertW
