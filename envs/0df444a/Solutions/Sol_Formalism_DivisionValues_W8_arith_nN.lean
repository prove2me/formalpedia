-- Prove2me | solution 1 for Formalism.DivisionValues.W8.arith_nN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:58.908603+00:00
-- url     : https://prove2.me/submissions/64e1c814-053c-486a-bee5-dd3fb1bb1c54

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open W8
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {n k N cs : ℝ} (hn : 0 ≤ n) (hnk : n ≤ k) (hkN : k ≤ N) (hcs : 0 ≤ cs) :
    n * (cs * N) ≤ cs * N ^ 2 := by
  have hN : 0 ≤ N := by linarith
  have h1 := mul_le_mul_of_nonneg_right (hnk.trans hkN) (mul_nonneg hcs hN)
  linarith
end Formalism.DivisionValues.W8
