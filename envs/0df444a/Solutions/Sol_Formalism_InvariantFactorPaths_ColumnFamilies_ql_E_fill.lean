-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_E_fill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:24.930924+00:00
-- url     : https://prove2.me/submissions/f6ca699f-0840-451e-a6e5-2b91ebbd728a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ql_E lo N (ql_fill lo N f) = f := by
  funext j
  have := j.2
  simp only [ql_E, ql_fill]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  ext
  show (lo + 1 + (j : ℕ) - lo - 1).toNat = j
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
