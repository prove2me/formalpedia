-- Prove2me | solution 1 for Formalism.DivisionValues.W8.top_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:13.866728+00:00
-- url     : https://prove2.me/submissions/7528c137-dccb-454b-93eb-82c0f364a976

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
theorem _root_.solution {n aT w : ℕ} {S Bl sh : ℝ} {ν ap : Multiset ℕ}
    (h : IsRowsTop n aT w S Bl sh ν ap) : 0 ≤ S ∧ 0 ≤ Bl := by
  obtain ⟨c, c', r, r0, blk, sm, hI, -, -, hblk, -, -⟩ := h
  exact ⟨le_trans (hI.1 0).1 (hI.1 0).2, le_trans (Nat.cast_nonneg _) hblk⟩
end Formalism.DivisionValues.W8
