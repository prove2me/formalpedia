-- Prove2me | solution 1 for Formalism.DivisionValues.W8.sum_univ_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:13.570703+00:00
-- url     : https://prove2.me/submissions/6a88f808-3a12-461c-8814-d18ea1f69221

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
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {n : ℕ} (g : Fin n → ℕ) :
    (((Finset.univ.val.map g).sum : ℕ) : ℝ) = ∑ i, (g i : ℝ) := by
  have h : (Finset.univ.val.map g).sum = ∑ i, g i := rfl
  rw [h, Nat.cast_sum]
end Formalism.DivisionValues.W8
